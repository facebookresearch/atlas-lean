/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Algebra.Homology.ExactSequence
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.HomotopyInvariance
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequence

import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Exact pair sequences

Exact-diagram lift of the homology pair sequence, named exactness at
consecutive terms, and vanishing of relative homology on diagonal pairs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u v

namespace TopPair

namespace HomologyTheoryData

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The property of being an exact sequence in `ComposableArrows C 4`. -/
abbrev isExactPairSequence (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :
    ObjectProperty (ComposableArrows C 4) :=
  ComposableArrows.exactSequences C 4

/-- The full subcategory of exact `4`-composable arrows, used for the pair sequence. -/
abbrev ExactPairSequence (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  ComposableArrows.ExactSequences C 4

/-- The exact pair sequence as a functor valued in the full subcategory of exact diagrams. -/
def exactPairSequenceFunctor (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) :
    TopPair.{w} ⥤ ExactPairSequence C :=
  (isExactPairSequence C).lift (E.pairSequenceFunctor n)
    (fun X => IsExact.exact_pairSequence (E := E) n X)

@[simp]
lemma exactPairSequenceFunctor_obj_obj (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (X : TopPair.{w}) :
    ((exactPairSequenceFunctor (C := C) E n).obj X).obj = E.pairSequence n X :=
  rfl

@[simp]
lemma exactPairSequenceFunctor_map_hom (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    {X Y : TopPair.{w}} (f : X ⟶ Y) :
    ((exactPairSequenceFunctor (C := C) E n).map f).hom = (E.pairSequenceFunctor n).map f :=
  rfl

/-- The exact pair sequence bifunctor, functorial in exact theories. -/
def exactPairSequenceBifunctor (n : ℤ) :
    (isExact (C := C)).FullSubcategory ⥤ (TopPair.{w} ⥤ ExactPairSequence C) where
  obj E := @exactPairSequenceFunctor _ _ _ E.obj E.property n
  map {E F} f :=
    { app := fun X => ObjectProperty.homMk (((pairSequenceBifunctor (C := C) n).map f.hom).app X)
      naturality := fun X Y g => by
        apply ObjectProperty.hom_ext
        exact ((pairSequenceBifunctor (C := C) n).map f.hom).naturality g }
  map_id E := by
    apply NatTrans.ext
    funext X
    apply ObjectProperty.hom_ext
    change ((pairSequenceBifunctor (C := C) n).map (𝟙 E.obj)).app X = 𝟙 _
    exact congrArg (fun k => k.app X) ((pairSequenceBifunctor (C := C) n).map_id E.obj)
  map_comp {E F G} f g := by
    apply NatTrans.ext
    funext X
    apply ObjectProperty.hom_ext
    change ((pairSequenceBifunctor (C := C) n).map (f.hom ≫ g.hom)).app X =
        ((pairSequenceBifunctor (C := C) n).map f.hom).app X ≫
          ((pairSequenceBifunctor (C := C) n).map g.hom).app X
    exact congrArg (fun k => k.app X) ((pairSequenceBifunctor (C := C) n).map_comp f.hom g.hom)

@[simp]
lemma exactPairSequenceBifunctor_obj_obj_obj
    (E : (isExact (C := C)).FullSubcategory) (n : ℤ) (X : TopPair.{w}) :
    (((exactPairSequenceBifunctor (C := C) n).obj E).obj X).obj =
      E.obj.pairSequence n X :=
  rfl

@[simp]
lemma exactPairSequenceBifunctor_map_app_hom
    {E F : (isExact (C := C)).FullSubcategory} (f : E ⟶ F)
    (n : ℤ) (X : TopPair.{w}) :
    (((exactPairSequenceBifunctor (C := C) n).map f).app X).hom =
      pairSequenceHom f.hom n X :=
  rfl

end HomologyTheoryData

end TopPair

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Consecutive boundary and subspace maps vanish. -/
theorem boundary_comp_subspaceMap
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) :
    E.boundary n P ≫ E.subspaceMap (n - 1) P = 0 := by
  have h := (IsExact.exact_pairSequence (E := E) n P).toIsComplex.zero 0
  change E.boundary n P ≫ E.subspaceMap (n - 1) P = 0 at h
  exact h

/-- Consecutive subspace and relative maps vanish. -/
theorem subspaceMap_comp_toRelative
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) :
    E.subspaceMap n P ≫ E.toRelative n P = 0 := by
  have h := (IsExact.exact_pairSequence (E := E) (n + 1) P).toIsComplex.zero 1
  change E.subspaceMap ((n + 1) - 1) P ≫ E.toRelative ((n + 1) - 1) P = 0 at h
  have hDegree : (n + 1) - 1 = n := by omega
  exact hDegree ▸ h

/-- Consecutive relative and boundary maps vanish. -/
theorem toRelative_comp_boundary
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) :
    E.toRelative n P ≫ E.boundary n P = 0 := by
  have h := (IsExact.exact_pairSequence (E := E) (n + 1) P).toIsComplex.zero 2
  change E.toRelative ((n + 1) - 1) P ≫ E.boundary ((n + 1) - 1) P = 0 at h
  have hDegree : (n + 1) - 1 = n := by omega
  exact hDegree ▸ h

/-- Exactness at the subspace term. -/
theorem exact_boundary_subspaceMap
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) :
    (ShortComplex.mk (E.boundary n P) (E.subspaceMap (n - 1) P)
      (boundary_comp_subspaceMap E n P)).Exact := by
  have h := (IsExact.exact_pairSequence (E := E) n P).exact 0
  change (ShortComplex.mk (E.boundary n P) (E.subspaceMap (n - 1) P) _).Exact at h
  exact h

/-- Exactness at the absolute term. -/
theorem exact_subspaceMap_toRelative
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) :
    (ShortComplex.mk (E.subspaceMap n P) (E.toRelative n P)
      (subspaceMap_comp_toRelative E n P)).Exact := by
  have h := (IsExact.exact_pairSequence (E := E) (n + 1) P).exact 1
  change (ShortComplex.mk (E.subspaceMap ((n + 1) - 1) P)
      (E.toRelative ((n + 1) - 1) P) _).Exact at h
  have hDegree : (n + 1) - 1 = n := by omega
  exact hDegree ▸ h

/-- Exactness at the relative term. -/
theorem exact_toRelative_boundary
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) :
    (ShortComplex.mk (E.toRelative n P) (E.boundary n P)
      (toRelative_comp_boundary E n P)).Exact := by
  have h := (IsExact.exact_pairSequence (E := E) (n + 1) P).exact 2
  change (ShortComplex.mk (E.toRelative ((n + 1) - 1) P)
      (E.boundary ((n + 1) - 1) P) _).Exact at h
  have hDegree : (n + 1) - 1 = n := by omega
  exact hDegree ▸ h

/-- A map of pairs induces an isomorphism on relative homology when it induces
isomorphisms on the absolute homology of both spaces in the two adjacent degrees. -/
theorem isIso_relativeMap_of_isIso_absoluteMaps
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) {P Q : TopPair.{w}} (f : P ⟶ Q)
    [IsIso ((E.H n).map (TopPair.Hom.snd f))]
    [IsIso ((E.H n).map (TopPair.Hom.fst f))]
    [IsIso ((E.H (n - 1)).map (TopPair.Hom.snd f))]
    [IsIso ((E.H (n - 1)).map (TopPair.Hom.fst f))] :
    IsIso ((E.Hₚ n).map f) := by
  let S : ComposableArrows C 4 :=
    ComposableArrows.mk₄
      (E.subspaceMap n P) (E.toRelative n P) (E.boundary n P)
        (E.subspaceMap (n - 1) P)
  let T : ComposableArrows C 4 :=
    ComposableArrows.mk₄
      (E.subspaceMap n Q) (E.toRelative n Q) (E.boundary n Q)
        (E.subspaceMap (n - 1) Q)
  let φ : S ⟶ T :=
    ComposableArrows.homMk₄
      ((E.H n).map (TopPair.Hom.snd f))
      ((E.H n).map (TopPair.Hom.fst f))
      ((E.Hₚ n).map f)
      ((E.H (n - 1)).map (TopPair.Hom.snd f))
      ((E.H (n - 1)).map (TopPair.Hom.fst f))
      ((E.subspaceMapNatTrans n).naturality f).symm
      ((E.toRelativeNatTrans n).naturality f).symm
      ((E.δ n (n - 1)).naturality f).symm
      ((E.subspaceMapNatTrans (n - 1)).naturality f).symm
  have hS : S.Exact :=
    ComposableArrows.exact_of_δ₀
      (exact_subspaceMap_toRelative E n P).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (exact_toRelative_boundary E n P).exact_toComposableArrows
        (exact_boundary_subspaceMap E n P).exact_toComposableArrows)
  have hT : T.Exact :=
    ComposableArrows.exact_of_δ₀
      (exact_subspaceMap_toRelative E n Q).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (exact_toRelative_boundary E n Q).exact_toComposableArrows
        (exact_boundary_subspaceMap E n Q).exact_toComposableArrows)
  change IsIso (ComposableArrows.app' φ 2)
  apply CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hS hT φ
  · change Epi ((E.H n).map (TopPair.Hom.snd f))
    infer_instance
  · change IsIso ((E.H n).map (TopPair.Hom.fst f))
    infer_instance
  · change IsIso ((E.H (n - 1)).map (TopPair.Hom.snd f))
    infer_instance
  · change Mono ((E.H (n - 1)).map (TopPair.Hom.fst f))
    infer_instance

/-- Relative homology vanishes when the subspace map is epi in degree `n` and
    mono in degree `n - 1`. -/
theorem isZero_relative_of_epi_subspaceMap_of_mono_subspaceMap
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w})
    [Epi (E.subspaceMap n P)] [Mono (E.subspaceMap (n - 1) P)] :
    IsZero ((E.Hₚ n).obj P) := by
  have hTo : E.toRelative n P = 0 :=
    (exact_subspaceMap_toRelative E n P).epi_f_iff.mp inferInstance
  have hBd : E.boundary n P = 0 :=
    (exact_boundary_subspaceMap E n P).mono_g_iff.mp inferInstance
  exact (exact_toRelative_boundary E n P).isZero_X₂ hTo hBd

/-- Relative homology vanishes when the subspace map is a homotopy equivalence. -/
theorem isZero_relative_of_homotopyEquiv
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) (P : TopPair.{w})
    (e : ContinuousMap.HomotopyEquiv P.snd P.fst)
    (he : TopCat.ofHom e.toFun = P.map) :
    IsZero ((E.Hₚ n).obj P) := by
  have : IsIso (E.subspaceMap n P) := by
    change IsIso ((E.H n).map P.map)
    rw [← he]
    exact (E.absoluteIsoOfHomotopyEquiv
      (X := P.snd) (Y := P.fst) e n).isIso_hom
  have : IsIso (E.subspaceMap (n - 1) P) := by
    change IsIso ((E.H (n - 1)).map P.map)
    rw [← he]
    exact (E.absoluteIsoOfHomotopyEquiv
      (X := P.snd) (Y := P.fst) e (n - 1)).isIso_hom
  exact isZero_relative_of_epi_subspaceMap_of_mono_subspaceMap E n P

/-- Relative homology vanishes when the subspace inclusion is an isomorphism. -/
theorem isZero_relative_of_isIso_map
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) [IsIso P.map] :
    IsZero ((E.Hₚ n).obj P) := by
  have : IsIso (E.subspaceMap n P) := by
    change IsIso ((E.H n).map P.map)
    infer_instance
  have : IsIso (E.subspaceMap (n - 1) P) := by
    change IsIso ((E.H (n - 1)).map P.map)
    infer_instance
  exact isZero_relative_of_epi_subspaceMap_of_mono_subspaceMap E n P

/-- Relative homology vanishes on the diagonal pair. -/
theorem isZero_relative_diag
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (X : TopCat.{w}) :
    IsZero ((E.Hₚ n).obj (TopPair.diag.obj X)) := by
  have : IsIso (TopPair.diag.obj X).map := by
    change IsIso (𝟙 X)
    infer_instance
  exact isZero_relative_of_isIso_map E n (TopPair.diag.obj X)

/-- Absolute homology of the empty space vanishes. -/
theorem isZero_absolute_pempty
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) :
    IsZero ((E.H n).obj (TopCat.of PEmpty.{w + 1})) := by
  let X := TopCat.of PEmpty.{w + 1}
  have : IsIso (TopPair.ofTopCat X).map :=
    (TopCat.isInitialPEmpty.uniqueUpToIso TopCat.isInitialPEmpty).isIso_hom
  have h : IsZero ((E.Hₚ n).obj (TopPair.ofTopCat X)) :=
    isZero_relative_of_isIso_map E n (TopPair.ofTopCat X)
  exact h.of_iso ((E.iso n).app X)

end TopPair.HomologyTheoryData.IsExact

namespace TopPair.GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Generalized homology of the empty space vanishes. -/
theorem isZero_absolute_pempty
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) :
    IsZero ((E.H n).obj (TopCat.of PEmpty.{w + 1})) :=
  TopPair.HomologyTheoryData.IsExact.isZero_absolute_pempty E.obj n

end TopPair.GeneralizedHomologyTheory

namespace TopPair.OrdinaryHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Ordinary homology of the empty space vanishes. -/
theorem isZero_absolute_pempty
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) :
    IsZero ((E.H n).obj (TopCat.of PEmpty.{w + 1})) :=
  TopPair.GeneralizedHomologyTheory.isZero_absolute_pempty
    (forgetDimension.obj E) n

end TopPair.OrdinaryHomologyTheory
