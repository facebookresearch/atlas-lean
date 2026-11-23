/-
Copyright (c) 2025 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeHomology
public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains.TwoSet
public import MathlibExt.AlgebraicTopology.SingularHomology.Subspace.Basic
public import MathlibExt.Topology.Category.TopPair.Excision

/-!
# Excision — relative-chain factorization via two-set pushout

This leaf provides the chain-level excision factorization:

* source pair `(A ∩ B, B)` and target pair `(A, X)` as `TopPair`,
* the induced `TopPair` morphism,
* identification of the source arrow with `mapInterRight`,
* the middle two-set arrow `mapInterRight → mapLeftBoth`,
* the target comparison `mapLeftBoth → singularPairChainArrow (A ⊂ X)`,
* their composite equals the functorial image of the `TopPair` map,
* after applying `coker`, the factorization

  `C(X,A∩B→B) → cokernel(mapInterRight) → cokernel(mapLeftBoth) → C(X,A)`

  via `excisionSourceRelIso`, `cokernelComparison`, and `excisionTargetComp`.

No openness hypotheses, no target quasi-isomorphism, no homology-level
excision are introduced here. The leaf is universe-polymorphic in both the
topology and coefficient category.-/

open CategoryTheory Limits AlgebraicTopology Topology

namespace AlgebraicTopology

universe w u v z

/-! ### Internal helpers (module-private) -/

private lemma smallChainMapOfLE_proof_irrel_aux {X : TopCat.{w}} {C : Type u}
    [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    {ι κ : Type} {U : ι → Set X} {V : κ → Set X} {R : C}
    (h1 : subordinateCover U ≤ subordinateCover V)
    (h2 : subordinateCover U ≤ subordinateCover V) :
    smallChainMapOfLE (C := C) R U V h1 =
      smallChainMapOfLE R U V h2 := by
  have eq1 : smallChainMapOfLE R U V h1 ≫ smallChainInclusion R V =
      smallChainInclusion R U :=
    smallChainMapOfLE_comp_inclusion _ _ _ _
  have eq2 : smallChainMapOfLE R U V h2 ≫ smallChainInclusion R V =
      smallChainInclusion R U :=
    smallChainMapOfLE_comp_inclusion _ _ _ _
  have hEq : smallChainMapOfLE R U V h1 ≫ smallChainInclusion R V =
      smallChainMapOfLE R U V h2 ≫ smallChainInclusion R V := by
    calc smallChainMapOfLE R U V h1 ≫ smallChainInclusion R V
        = smallChainInclusion R U := eq1
      _ = smallChainMapOfLE R U V h2 ≫ smallChainInclusion R V := eq2.symm
  exact (cancel_mono (smallChainInclusion R V)).mp hEq

section GenericCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

private noncomputable def isoInterDef_aux (X : TopCat.{w}) (A B : Set X)
    (R : C) :
    ((singularChainComplexFunctor C).obj R).obj
        (TopCat.of ↥(A ∩ B)) ≅ chainInter A B R :=
  subspaceChainIsoSubcomplex (A ∩ B) R

private noncomputable def isoADef_aux (X : TopCat.{w}) (A : Set X)
    (R : C) :
    ((singularChainComplexFunctor C).obj R).obj
        (TopCat.of ↥A) ≅ chainLeft A R :=
  subspaceChainIsoSubcomplex A R

private noncomputable def isoBDef_aux (X : TopCat.{w}) (B : Set X)
    (R : C) :
    ((singularChainComplexFunctor C).obj R).obj
        (TopCat.of ↥B) ≅ chainRight B R :=
  subspaceChainIsoSubcomplex B R

/-! ### Public API -/

/-- Source topological pair `(A ∩ B, B)` for excision. -/
public noncomputable abbrev excisionSourcePair (X : TopCat.{w}) (A B : Set X) : TopPair :=
  TopPair.excisionSource X A B

/-- Target topological pair `(A, X)` for excision. -/
public noncomputable abbrev excisionTargetPair (X : TopCat.{w}) (A : Set X) : TopPair :=
  TopPair.excisionTarget X A

/-- The `TopPair` morphism `(A ∩ B ↪ B) → (A ↪ X)`. -/
public noncomputable abbrev excisionTopPairHom (X : TopCat.{w}) (A B : Set X) :
    excisionSourcePair X A B ⟶ excisionTargetPair X A :=
  TopPair.excisionHom X A B

@[simp]
public theorem excisionTopPairHom_fst (X : TopCat.{w}) (A B : Set X) :
    TopPair.Hom.fst (excisionTopPairHom X A B) = subspaceIncl B := by
  rfl

@[simp]
public theorem excisionTopPairHom_snd (X : TopCat.{w}) (A B : Set X) :
    TopPair.Hom.snd (excisionTopPairHom X A B) =
      subspaceInclOfSubset (Set.inter_subset_left : A ∩ B ⊆ A) := by
  rfl

@[expose] public noncomputable def excisionSourceArrow (X : TopCat.{w})
    (A B : Set X) (R : C) :
    Arrow (ChainComplex C ℕ) :=
  (singularPairChainArrowFunctor C R).obj
    (excisionSourcePair X A B)

@[expose] public noncomputable def excisionTargetArrow (X : TopCat.{w})
    (A : Set X) (R : C) :
    Arrow (ChainComplex C ℕ) :=
  (singularPairChainArrowFunctor C R).obj
    (excisionTargetPair X A)

/-- Identify the source arrow with `mapInterRight`. -/
public noncomputable def excisionSourceArrowIso (X : TopCat.{w})
    (A B : Set X) (R : C) :
    excisionSourceArrow X A B R ≅ Arrow.mk (mapInterRight A B R) := by
  dsimp [excisionSourceArrow, excisionSourcePair]
  let isoLeft :
      ((singularChainComplexFunctor C).obj R).obj
          (TopCat.of ↥(A ∩ B)) ≅ chainInter A B R :=
    subspaceChainIsoSubcomplex (A ∩ B) R
  let isoRight :
      ((singularChainComplexFunctor C).obj R).obj
          (TopCat.of ↥B) ≅ chainRight B R :=
    subspaceChainIsoSubcomplex B R
  have hNat : isoLeft.hom ≫ mapInterRight A B R =
      ((singularChainComplexFunctor C).obj R).map
        (subspaceInclOfSubset (Set.inter_subset_right : A ∩ B ⊆ B)) ≫
        isoRight.hom := by
    have hNat0 :=
      subspaceChainIsoSubcomplex_naturality_inclusion
        (S := A ∩ B) (T := B) (Set.inter_subset_right) R
    have hMapEq1 :
        smallChainMapOfLE R (fun _ : Unit => A ∩ B) (fun _ : Unit => B)
          (by
            rw [subordinateCover_singleton, subordinateCover_singleton]
            exact subordinateSet_mono (Set.inter_subset_right)) =
          smallChainMapOfLE R (fun _ : Unit => A ∩ B) (fun _ : Unit => B)
            (subCxInter_le_right A B) :=
      smallChainMapOfLE_proof_irrel_aux _ _
    have hMapEq2 :
        smallChainMapOfLE R (fun _ : Unit => A ∩ B) (fun _ : Unit => B)
            (subCxInter_le_right A B) = mapInterRight A B R := rfl
    have hMapEq :
        smallChainMapOfLE R (fun _ : Unit => A ∩ B) (fun _ : Unit => B)
          (by
            rw [subordinateCover_singleton, subordinateCover_singleton]
            exact subordinateSet_mono (Set.inter_subset_right)) =
          mapInterRight A B R :=
      hMapEq1.trans hMapEq2
    rw [hMapEq] at hNat0
    exact hNat0
  exact Arrow.isoMk isoLeft isoRight hNat

@[expose] public noncomputable def excisionMiddleArrowHom (X : TopCat.{w})
    (A B : Set X) (R : C) :
    Arrow.mk (mapInterRight A B R) ⟶ Arrow.mk (mapLeftBoth A B R) :=
  Arrow.homMk (mapInterLeft A B R) (mapRightBoth A B R)
    (squareTwoSet A B R)

@[expose] public noncomputable def excisionTargetArrowHom (X : TopCat.{w})
    (A B : Set X) (R : C) :
    Arrow.mk (mapLeftBoth A B R) ⟶ excisionTargetArrow X A R := by
  dsimp [excisionTargetArrow, excisionTargetPair]
  let isoA :
      ((singularChainComplexFunctor C).obj R).obj
          (TopCat.of ↥A) ≅ chainLeft A R :=
    subspaceChainIsoSubcomplex A R
  refine Arrow.homMk isoA.inv
    (smallChainInclusion R (smallCoverBoth A B)) ?_
  have hInclBoth :
      mapLeftBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B) =
        smallChainInclusion R (smallCoverLeft A) :=
    smallChainMapOfLE_comp_inclusion _ _ _ _
  have hIsoComp :
      isoA.hom ≫ smallChainInclusion R (smallCoverLeft A) =
        ((singularChainComplexFunctor C).obj R).map
          (subspaceIncl A) :=
    subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion A R
  have hInvComp :
      smallChainInclusion R (smallCoverLeft A) =
        isoA.inv ≫
          ((singularChainComplexFunctor C).obj R).map
            (subspaceIncl A) := by
    have h1 :
        smallChainInclusion R (smallCoverLeft A) =
          (𝟙 (chainLeft A R)) ≫ smallChainInclusion R (smallCoverLeft A) :=
      (Category.id_comp _).symm
    have h2 :
        (𝟙 (chainLeft A R)) ≫ smallChainInclusion R (smallCoverLeft A) =
          (isoA.inv ≫ isoA.hom) ≫ smallChainInclusion R (smallCoverLeft A) := by
      rw [← isoA.inv_hom_id]
    have h3 :
        (isoA.inv ≫ isoA.hom) ≫ smallChainInclusion R (smallCoverLeft A) =
          isoA.inv ≫ (isoA.hom ≫ smallChainInclusion R (smallCoverLeft A)) :=
      Category.assoc isoA.inv isoA.hom _
    have h4 :
        isoA.inv ≫ (isoA.hom ≫ smallChainInclusion R (smallCoverLeft A)) =
          isoA.inv ≫
            ((singularChainComplexFunctor C).obj R).map
              (subspaceIncl A) :=
      congrArg (fun t => isoA.inv ≫ t) hIsoComp
    exact h1.trans (h2.trans (h3.trans h4))
  exact (hInvComp.symm.trans hInclBoth.symm)

@[expose] public noncomputable def excisionCompositeArrowHom (X : TopCat.{w})
    (A B : Set X) (R : C) :
    excisionSourceArrow X A B R ⟶ excisionTargetArrow X A R :=
  (excisionSourceArrowIso X A B R).hom ≫
    (excisionMiddleArrowHom X A B R ≫ excisionTargetArrowHom X A B R)

public lemma excisionArrowEq (X : TopCat.{w}) (A B : Set X)
    (R : C) :
    excisionCompositeArrowHom X A B R =
      (singularPairChainArrowFunctor C R).map
        (excisionTopPairHom X A B) := by
  apply Arrow.hom_ext
  · dsimp [excisionCompositeArrowHom, excisionSourceArrowIso,
      excisionMiddleArrowHom, excisionTargetArrowHom, excisionTopPairHom,
      excisionSourcePair, excisionTargetPair, excisionSourceArrow,
      excisionTargetArrow, singularPairChainArrowFunctor,
      topPairArrowFunctor]
    have hNat0 :=
      subspaceChainIsoSubcomplex_naturality_inclusion
        (S := A ∩ B) (T := A) (Set.inter_subset_left) R
    have hMapEq1 :
        smallChainMapOfLE R (fun _ : Unit => A ∩ B) (fun _ : Unit => A)
          (by
            rw [subordinateCover_singleton, subordinateCover_singleton]
            exact subordinateSet_mono (Set.inter_subset_left)) =
          smallChainMapOfLE R (fun _ : Unit => A ∩ B) (fun _ : Unit => A)
            (subCxInter_le_left A B) :=
      smallChainMapOfLE_proof_irrel_aux _ _
    have hMapEq2 :
        smallChainMapOfLE R (fun _ : Unit => A ∩ B) (fun _ : Unit => A)
            (subCxInter_le_left A B) = mapInterLeft A B R := rfl
    have hMapEq :
        smallChainMapOfLE R (fun _ : Unit => A ∩ B) (fun _ : Unit => A)
          (by
            rw [subordinateCover_singleton, subordinateCover_singleton]
            exact subordinateSet_mono (Set.inter_subset_left)) =
          mapInterLeft A B R :=
      hMapEq1.trans hMapEq2
    rw [hMapEq] at hNat0
    have hNat :
        (isoInterDef_aux X A B R).hom ≫ mapInterLeft A B R =
          ((singularChainComplexFunctor C).obj R).map
              (subspaceInclOfSubset
                (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
            (isoADef_aux X A R).hom := by
      have h1 :
          (isoInterDef_aux X A B R).hom ≫ mapInterLeft A B R =
            (subspaceChainIsoSubcomplex (A ∩ B) R).hom ≫
              mapInterLeft A B R := rfl
      have h2 :
          (subspaceChainIsoSubcomplex (A ∩ B) R).hom ≫
              mapInterLeft A B R =
            ((singularChainComplexFunctor C).obj R).map
                (subspaceInclOfSubset
                  (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
              (subspaceChainIsoSubcomplex A R).hom := hNat0
      have h3 :
          ((singularChainComplexFunctor C).obj R).map
                (subspaceInclOfSubset
                  (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
              (subspaceChainIsoSubcomplex A R).hom =
            ((singularChainComplexFunctor C).obj R).map
                (subspaceInclOfSubset
                  (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
              (isoADef_aux X A R).hom := rfl
      exact h1.trans (h2.trans h3)
    have h1 :
        (isoInterDef_aux X A B R).hom ≫
            (mapInterLeft A B R ≫ (isoADef_aux X A R).inv) =
          ((isoInterDef_aux X A B R).hom ≫ mapInterLeft A B R) ≫
            (isoADef_aux X A R).inv := by
      rw [Category.assoc]
    have h2 :
        ((isoInterDef_aux X A B R).hom ≫ mapInterLeft A B R) ≫
            (isoADef_aux X A R).inv =
          (((singularChainComplexFunctor C).obj R).map
                (subspaceInclOfSubset
                  (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
              (isoADef_aux X A R).hom) ≫ (isoADef_aux X A R).inv := by
      rw [hNat]
    have h3 :
        (((singularChainComplexFunctor C).obj R).map
              (subspaceInclOfSubset
                (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
            (isoADef_aux X A R).hom) ≫ (isoADef_aux X A R).inv =
          ((singularChainComplexFunctor C).obj R).map
              (subspaceInclOfSubset
                (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
            ((isoADef_aux X A R).hom ≫ (isoADef_aux X A R).inv) := by
      rw [Category.assoc]
    have h4 :
        ((singularChainComplexFunctor C).obj R).map
              (subspaceInclOfSubset
                (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
            ((isoADef_aux X A R).hom ≫ (isoADef_aux X A R).inv) =
          ((singularChainComplexFunctor C).obj R).map
              (subspaceInclOfSubset
                (Set.inter_subset_left : A ∩ B ⊆ A)) := by
      rw [Iso.hom_inv_id, Category.comp_id]
    calc (isoInterDef_aux X A B R).hom ≫
          (mapInterLeft A B R ≫ (isoADef_aux X A R).inv)
        = ((isoInterDef_aux X A B R).hom ≫ mapInterLeft A B R) ≫
            (isoADef_aux X A R).inv := h1
      _ = (((singularChainComplexFunctor C).obj R).map
              (subspaceInclOfSubset
                (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
            (isoADef_aux X A R).hom) ≫ (isoADef_aux X A R).inv := h2
      _ = ((singularChainComplexFunctor C).obj R).map
              (subspaceInclOfSubset
                (Set.inter_subset_left : A ∩ B ⊆ A)) ≫
            ((isoADef_aux X A R).hom ≫ (isoADef_aux X A R).inv) := h3
      _ = ((singularChainComplexFunctor C).obj R).map
            (subspaceInclOfSubset
              (Set.inter_subset_left : A ∩ B ⊆ A)) := h4
  · dsimp [excisionCompositeArrowHom, excisionSourceArrowIso,
      excisionMiddleArrowHom, excisionTargetArrowHom, excisionTopPairHom,
      excisionSourcePair, excisionTargetPair, excisionSourceArrow,
      excisionTargetArrow, singularPairChainArrowFunctor,
      topPairArrowFunctor]
    have hInclRight :
        mapRightBoth A B R ≫ smallChainInclusion R (smallCoverBoth A B) =
          smallChainInclusion R (smallCoverRight B) :=
      smallChainMapOfLE_comp_inclusion _ _ _ _
    have hIsoRight :
        (isoBDef_aux X B R).hom ≫
            smallChainInclusion R (smallCoverRight B) =
          ((singularChainComplexFunctor C).obj R).map
            (subspaceIncl B) :=
      subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion B R
    have h1 :
        (isoBDef_aux X B R).hom ≫
            (mapRightBoth A B R ≫
              smallChainInclusion R (smallCoverBoth A B)) =
          (isoBDef_aux X B R).hom ≫
            smallChainInclusion R (smallCoverRight B) := by
      rw [hInclRight]
    have h2 :
        (isoBDef_aux X B R).hom ≫
            smallChainInclusion R (smallCoverRight B) =
          ((singularChainComplexFunctor C).obj R).map
            (subspaceIncl B) := hIsoRight
    exact (h1.trans h2)

@[expose] public noncomputable def cokerFunctor :
    Arrow (ChainComplex C ℕ) ⥤
      ChainComplex C ℕ :=
  coker (C := ChainComplex C ℕ)

public noncomputable def excisionSourceRelIso (X : TopCat.{w}) (A B : Set X)
    (R : C) :
    (relativeSingularChainFunctor C R).obj
        (excisionSourcePair X A B) ≅ cokernel (mapInterRight A B R) :=
  cokerFunctor.mapIso (excisionSourceArrowIso X A B R)

/-- The defining cokernel characteristic of the excision source comparison. -/
@[reassoc]
public lemma relativeSingularChainQuotient_comp_excisionSourceRelIso
    (X : TopCat.{w}) (A B : Set X) (R : C) :
    relativeSingularChainQuotient C R (excisionSourcePair X A B) ≫
        (excisionSourceRelIso X A B R).hom =
      (excisionSourceArrowIso X A B R).hom.right ≫
        cokernel.π (mapInterRight A B R) := by
  change
    (coker.π (C := ChainComplex C ℕ)).app (excisionSourceArrow X A B R) ≫
        (coker (C := ChainComplex C ℕ)).map
          (excisionSourceArrowIso X A B R).hom =
      (excisionSourceArrowIso X A B R).hom.right ≫
        (coker.π (C := ChainComplex C ℕ)).app
          (Arrow.mk (mapInterRight A B R))
  exact ((coker.π (C := ChainComplex C ℕ)).naturality
    (excisionSourceArrowIso X A B R).hom).symm

@[expose] public noncomputable def excisionTargetComp (X : TopCat.{w})
    (A B : Set X) (R : C) :
    cokernel (mapLeftBoth A B R) ⟶
      (relativeSingularChainFunctor C R).obj
        (excisionTargetPair X A) :=
  cokerFunctor.map (excisionTargetArrowHom X A B R)

/-- The defining cokernel characteristic of the excision target comparison. -/
@[reassoc]
public lemma cokernel_π_comp_excisionTargetComp
    (X : TopCat.{w}) (A B : Set X) (R : C) :
    cokernel.π (mapLeftBoth A B R) ≫
        excisionTargetComp X A B R =
      smallChainInclusion R (smallCoverBoth A B) ≫
        relativeSingularChainQuotient C R
          (excisionTargetPair X A) := by
  apply cokernel.π_desc

public lemma excisionMiddleCokerEq (X : TopCat.{w}) (A B : Set X)
    (R : C) :
    cokerFunctor.map (excisionMiddleArrowHom X A B R) =
      cokernelComparison A B R := rfl

public lemma excisionFactorization (X : TopCat.{w}) (A B : Set X)
    (R : C) :
    (relativeSingularChainFunctor C R).map
        (excisionTopPairHom X A B) =
      (excisionSourceRelIso X A B R).hom ≫
        (cokernelComparison A B R ≫ excisionTargetComp X A B R) := by
  have hArrow :
      (singularPairChainArrowFunctor C R).map
          (excisionTopPairHom X A B) =
        excisionCompositeArrowHom X A B R :=
    (excisionArrowEq X A B R).symm
  have hRel :
      (relativeSingularChainFunctor C R).map
          (excisionTopPairHom X A B) =
        cokerFunctor.map
          ((singularPairChainArrowFunctor C R).map
            (excisionTopPairHom X A B)) := rfl
  have hComp :
      cokerFunctor.map (excisionCompositeArrowHom X A B R) =
        cokerFunctor.map (excisionSourceArrowIso X A B R).hom ≫
          (cokerFunctor.map (excisionMiddleArrowHom X A B R) ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)) := by
    simp only [excisionCompositeArrowHom, Functor.map_comp]
  have h1 :
      (relativeSingularChainFunctor C R).map
          (excisionTopPairHom X A B) =
        cokerFunctor.map (excisionCompositeArrowHom X A B R) := by
    have ha :
        cokerFunctor.map
            ((singularPairChainArrowFunctor C R).map
              (excisionTopPairHom X A B)) =
          cokerFunctor.map (excisionCompositeArrowHom X A B R) :=
      congrArg cokerFunctor.map hArrow
    exact hRel.trans ha
  have h2 :
      cokerFunctor.map (excisionCompositeArrowHom X A B R) =
        cokerFunctor.map (excisionSourceArrowIso X A B R).hom ≫
          (cokerFunctor.map (excisionMiddleArrowHom X A B R) ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)) := hComp
  have h3 :
      cokerFunctor.map (excisionSourceArrowIso X A B R).hom =
        (excisionSourceRelIso X A B R).hom := rfl
  have h4 :
      cokerFunctor.map (excisionMiddleArrowHom X A B R) =
        cokernelComparison A B R := rfl
  have h5 :
      cokerFunctor.map (excisionTargetArrowHom X A B R) =
        excisionTargetComp X A B R := rfl
  have h6 :
      (relativeSingularChainFunctor C R).map
          (excisionTopPairHom X A B) =
        cokerFunctor.map (excisionSourceArrowIso X A B R).hom ≫
          (cokerFunctor.map (excisionMiddleArrowHom X A B R) ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)) :=
    h1.trans h2
  have h7 :
      cokerFunctor.map (excisionSourceArrowIso X A B R).hom ≫
          (cokerFunctor.map (excisionMiddleArrowHom X A B R) ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)) =
        (excisionSourceRelIso X A B R).hom ≫
          (cokerFunctor.map (excisionMiddleArrowHom X A B R) ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)) :=
    congrArg
      (fun f =>
        f ≫
          (cokerFunctor.map (excisionMiddleArrowHom X A B R) ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)))
      h3
  have h8a :
      (excisionSourceRelIso X A B R).hom ≫
          (cokerFunctor.map (excisionMiddleArrowHom X A B R) ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)) =
        (excisionSourceRelIso X A B R).hom ≫
          (cokernelComparison A B R ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)) :=
    congrArg
      (fun f =>
        (excisionSourceRelIso X A B R).hom ≫
          (f ≫ cokerFunctor.map (excisionTargetArrowHom X A B R)))
      h4
  have h8b :
      (excisionSourceRelIso X A B R).hom ≫
          (cokernelComparison A B R ≫
            cokerFunctor.map (excisionTargetArrowHom X A B R)) =
        (excisionSourceRelIso X A B R).hom ≫
          (cokernelComparison A B R ≫ excisionTargetComp X A B R) :=
    congrArg
      (fun f =>
        (excisionSourceRelIso X A B R).hom ≫ (cokernelComparison A B R ≫ f))
      h5
  exact h6.trans (h7.trans (h8a.trans h8b))

end GenericCoefficients

end AlgebraicTopology
