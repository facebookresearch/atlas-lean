/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakCobaseChange

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWColimits
import MathlibExt.AlgebraicTopology.SingularSet.Coproducts
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Data.Fintype.EquivFin

/-!
# Coproducts of realization weak equivalences

Arbitrary same-universe coproducts of realization weak equivalences of
simplicial sets are realization weak equivalences. Binary coproducts are two
cobase changes along coproduct inclusions. Finite coproducts follow by a
canonical head/tail decomposition. An arbitrary coproduct is the filtered
colimit of its finite subcoproducts; after realization and singularization,
the filtered-colimit theorem for weak equivalences between Kan complexes
applies.

This file installs only same-universe coproduct stability. It installs no
model structure and no filtered-colimit stability instance for realization
weak equivalences, and makes no Bousfield--Kan or diagonal claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MorphismProperty

universe u v

namespace SSet

/-- A binary coproduct of realization weak equivalences is a realization
weak equivalence. -/
theorem coprod_map_mem_realizationWeakEquivalences
    {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : realizationWeakEquivalences f)
    (hg : realizationWeakEquivalences g) :
    realizationWeakEquivalences (coprod.map f g) := by
  let _ : Mono (coprod.inl : A ⟶ A ⨿ C) := by
    rw [NatTrans.mono_iff_mono_app]
    intro a
    let ev : SSet.{u} ⥤ Type u :=
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj a
    let c : BinaryCofan (ev.obj A) (ev.obj C) :=
      BinaryCofan.mk (ev.map (coprod.inl : A ⟶ A ⨿ C))
        (ev.map (coprod.inr : C ⟶ A ⨿ C))
    change Mono c.inl
    exact MonoCoprod.binaryCofan_inl c
      (isColimitOfHasBinaryCoproductOfPreservesColimit ev A C)
  let _ : Mono (coprod.inl : C ⟶ C ⨿ B) := by
    rw [NatTrans.mono_iff_mono_app]
    intro a
    let ev : SSet.{u} ⥤ Type u :=
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj a
    let c : BinaryCofan (ev.obj C) (ev.obj B) :=
      BinaryCofan.mk (ev.map (coprod.inl : C ⟶ C ⨿ B))
        (ev.map (coprod.inr : B ⟶ C ⨿ B))
    change Mono c.inl
    exact MonoCoprod.binaryCofan_inl c
      (isColimitOfHasBinaryCoproductOfPreservesColimit ev C B)
  have hleft : realizationWeakEquivalences (coprod.map f (𝟙 C)) :=
    realizationWeakEquivalences.of_isPushout_mono
      (IsPushout.of_coprod_inl_with_id f C) hf
  have hswapped : realizationWeakEquivalences (coprod.map g (𝟙 B)) :=
    realizationWeakEquivalences.of_isPushout_mono
      (IsPushout.of_coprod_inl_with_id g B) hg
  have hright : realizationWeakEquivalences (coprod.map (𝟙 B) g) := by
    have hconj : coprod.map (𝟙 B) g =
        (coprod.braiding B C).hom ≫ coprod.map g (𝟙 B) ≫
          (coprod.braiding D B).hom := by
      ext <;> simp
    rw [hconj]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr hswapped)
  have hcomp : realizationWeakEquivalences
      (coprod.map f (𝟙 C) ≫ coprod.map (𝟙 B) g) :=
    MorphismProperty.comp_mem _ _ _ hleft hright
  have heq : coprod.map f (𝟙 C) ≫ coprod.map (𝟙 B) g =
      coprod.map f g := by
    ext <;> simp
  simpa only [heq] using hcomp

private noncomputable def sigmaFinSuccCofan
    (n : ℕ) (X : Fin (n + 1) → SSet.{u}) : Cofan X :=
  Cofan.mk (X 0 ⨿ (∐ fun i : Fin n => X i.succ))
    (fun i => Fin.cases coprod.inl
      (fun j => Sigma.ι (fun i : Fin n => X i.succ) j ≫ coprod.inr) i)

private noncomputable def sigmaFinSuccCofanIsColimit
    (n : ℕ) (X : Fin (n + 1) → SSet.{u}) :
    IsColimit (sigmaFinSuccCofan n X) :=
  Cofan.IsColimit.mk _
    (fun s => coprod.desc (s.inj 0)
      (Sigma.desc fun i : Fin n => s.inj i.succ))
    (by
      intro s i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [sigmaFinSuccCofan]
      · simp [sigmaFinSuccCofan])
    (by
      intro s m hm
      apply BinaryCofan.IsColimit.hom_ext (coprodIsCoprod _ _)
      · simpa [sigmaFinSuccCofan] using hm 0
      · apply Sigma.hom_ext
        intro i
        have hi := hm i.succ
        change (Sigma.ι (fun i : Fin n => X i.succ) i ≫ coprod.inr) ≫ m =
          s.inj i.succ at hi
        calc
          Sigma.ι (fun i : Fin n => X i.succ) i ≫ coprod.inr ≫ m =
              (Sigma.ι (fun i : Fin n => X i.succ) i ≫ coprod.inr) ≫ m :=
            (Category.assoc _ _ _).symm
          _ = s.inj i.succ := hi
          _ = Sigma.ι (fun i : Fin n => X i.succ) i ≫
              coprod.inr ≫ coprod.desc (s.inj 0)
                (Sigma.desc fun i : Fin n => s.inj i.succ) := by simp)

/-- Canonical decomposition of a coproduct indexed by `Fin (n+1)` into its
zeroth summand and the coproduct of successor summands. -/
private noncomputable def sigmaFinSuccIso
    (n : ℕ) (X : Fin (n + 1) → SSet.{u}) :
    (∐ X) ≅ X 0 ⨿ (∐ fun i : Fin n => X i.succ) :=
  IsColimit.coconePointUniqueUpToIso
    (coproductIsCoproduct X) (sigmaFinSuccCofanIsColimit n X)

private theorem sigmaFinSuccIso_hom_ι_zero
    (n : ℕ) (X : Fin (n + 1) → SSet.{u}) :
    Sigma.ι X 0 ≫ (sigmaFinSuccIso n X).hom = coprod.inl := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct X) (sigmaFinSuccCofanIsColimit n X) ⟨0⟩

private theorem sigmaFinSuccIso_hom_ι_succ
    (n : ℕ) (X : Fin (n + 1) → SSet.{u}) (i : Fin n) :
    Sigma.ι X i.succ ≫ (sigmaFinSuccIso n X).hom =
      Sigma.ι (fun j : Fin n => X j.succ) i ≫ coprod.inr := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct X) (sigmaFinSuccCofanIsColimit n X) ⟨i.succ⟩

private theorem sigmaFinSuccIso_naturality
    (n : ℕ) {X Y : Fin (n + 1) → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) :
    (sigmaFinSuccIso n X).hom ≫
        coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ) =
      Limits.Sigma.map f ≫ (sigmaFinSuccIso n Y).hom := by
  apply Sigma.hom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · calc
      Sigma.ι X 0 ≫ ((sigmaFinSuccIso n X).hom ≫
          coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ)) =
          (Sigma.ι X 0 ≫ (sigmaFinSuccIso n X).hom) ≫
            coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ) :=
        (Category.assoc _ _ _).symm
      _ = coprod.inl ≫
          coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ) := by
        rw [sigmaFinSuccIso_hom_ι_zero]
      _ = f 0 ≫ coprod.inl := coprod.inl_map _ _
      _ = f 0 ≫ (Sigma.ι Y 0 ≫ (sigmaFinSuccIso n Y).hom) := by
        rw [sigmaFinSuccIso_hom_ι_zero]
      _ = (f 0 ≫ Sigma.ι Y 0) ≫ (sigmaFinSuccIso n Y).hom :=
        (Category.assoc _ _ _).symm
      _ = (Sigma.ι X 0 ≫ Limits.Sigma.map f) ≫
          (sigmaFinSuccIso n Y).hom := by rw [Sigma.ι_map]
      _ = Sigma.ι X 0 ≫
          (Limits.Sigma.map f ≫ (sigmaFinSuccIso n Y).hom) :=
        Category.assoc _ _ _
  · calc
      Sigma.ι X j.succ ≫ ((sigmaFinSuccIso n X).hom ≫
          coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ)) =
          (Sigma.ι X j.succ ≫ (sigmaFinSuccIso n X).hom) ≫
            coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ) :=
        (Category.assoc _ _ _).symm
      _ = (Sigma.ι (fun i : Fin n => X i.succ) j ≫ coprod.inr) ≫
          coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ) := by
        rw [sigmaFinSuccIso_hom_ι_succ]
      _ = Sigma.ι (fun i : Fin n => X i.succ) j ≫
          (coprod.inr ≫
            coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ)) :=
        Category.assoc _ _ _
      _ = Sigma.ι (fun i : Fin n => X i.succ) j ≫
          (Limits.Sigma.map (fun i : Fin n => f i.succ) ≫ coprod.inr) := by
        rw [coprod.inr_map]
      _ = (Sigma.ι (fun i : Fin n => X i.succ) j ≫
          Limits.Sigma.map (fun i : Fin n => f i.succ)) ≫ coprod.inr :=
        (Category.assoc _ _ _).symm
      _ = (f j.succ ≫ Sigma.ι (fun i : Fin n => Y i.succ) j) ≫
          coprod.inr := by rw [Sigma.ι_map]
      _ = f j.succ ≫
          (Sigma.ι (fun i : Fin n => Y i.succ) j ≫ coprod.inr) :=
        Category.assoc _ _ _
      _ = f j.succ ≫
          (Sigma.ι Y j.succ ≫ (sigmaFinSuccIso n Y).hom) := by
        rw [sigmaFinSuccIso_hom_ι_succ]
      _ = (f j.succ ≫ Sigma.ι Y j.succ) ≫
          (sigmaFinSuccIso n Y).hom := (Category.assoc _ _ _).symm
      _ = (Sigma.ι X j.succ ≫ Limits.Sigma.map f) ≫
          (sigmaFinSuccIso n Y).hom := by rw [Sigma.ι_map]
      _ = Sigma.ι X j.succ ≫
          (Limits.Sigma.map f ≫ (sigmaFinSuccIso n Y).hom) :=
        Category.assoc _ _ _

private theorem sigma_map_mem_realizationWeakEquivalences_fin
    (n : ℕ) {X Y : Fin n → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, realizationWeakEquivalences (f i)) :
    realizationWeakEquivalences (Limits.Sigma.map f) := by
  induction n with
  | zero =>
      have hX : IsInitial (∐ X) := IsInitial.ofUniqueHom
        (fun Z => Sigma.desc (fun i => Fin.elim0 i)) (by
          intro Z g
          apply Sigma.hom_ext
          intro i
          exact Fin.elim0 i)
      have hY : IsInitial (∐ Y) := IsInitial.ofUniqueHom
        (fun Z => Sigma.desc (fun i => Fin.elim0 i)) (by
          intro Z g
          apply Sigma.hom_ext
          intro i
          exact Fin.elim0 i)
      let e : (∐ X) ≅ (∐ Y) := hX.uniqueUpToIso hY
      have heq : Limits.Sigma.map f = e.hom := hX.hom_ext _ _
      rw [heq]
      exact MorphismProperty.of_isIso realizationWeakEquivalences e.hom
  | succ n ih =>
      have htail : realizationWeakEquivalences
          (Limits.Sigma.map fun i : Fin n => f i.succ) :=
        ih (fun i => f i.succ) (fun i => hf i.succ)
      have hbinary : realizationWeakEquivalences
          (coprod.map (f 0) (Limits.Sigma.map fun i : Fin n => f i.succ)) :=
        coprod_map_mem_realizationWeakEquivalences _ _ (hf 0) htail
      let e : Arrow.mk (Limits.Sigma.map f) ≅
          Arrow.mk (coprod.map (f 0)
            (Limits.Sigma.map fun i : Fin n => f i.succ)) :=
        Arrow.isoMk (sigmaFinSuccIso n X) (sigmaFinSuccIso n Y)
          (sigmaFinSuccIso_naturality n f)
      exact (realizationWeakEquivalences.arrow_mk_iso_iff e).2 hbinary

/-- A finite coproduct of realization weak equivalences is a realization
weak equivalence. -/
theorem sigma_map_mem_realizationWeakEquivalences_of_finite
    {ι : Type v} [Finite ι] {X Y : ι → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, realizationWeakEquivalences (f i)) :
    realizationWeakEquivalences (Limits.Sigma.map f) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let X' : Fin (Fintype.card ι) → SSet.{u} := fun i => X (e.symm i)
  let Y' : Fin (Fintype.card ι) → SSet.{u} := fun i => Y (e.symm i)
  let f' : ∀ i, X' i ⟶ Y' i := fun i => f (e.symm i)
  have hf' : realizationWeakEquivalences (Limits.Sigma.map f') :=
    sigma_map_mem_realizationWeakEquivalences_fin _ f'
      (fun i => hf (e.symm i))
  have hnat : (Sigma.reindex e.symm X).hom ≫ Limits.Sigma.map f =
      Limits.Sigma.map f' ≫ (Sigma.reindex e.symm Y).hom := by
    apply Sigma.hom_ext
    intro i
    have hX : Sigma.ι X' i ≫ (Sigma.reindex e.symm X).hom =
        Sigma.ι X (e.symm i) := by
      change Sigma.ι (X ∘ e.symm) i ≫ (Sigma.reindex e.symm X).hom = _
      exact Sigma.ι_reindex_hom e.symm X i
    have hY : Sigma.ι Y' i ≫ (Sigma.reindex e.symm Y).hom =
        Sigma.ι Y (e.symm i) := by
      change Sigma.ι (Y ∘ e.symm) i ≫ (Sigma.reindex e.symm Y).hom = _
      exact Sigma.ι_reindex_hom e.symm Y i
    calc
      Sigma.ι X' i ≫ ((Sigma.reindex e.symm X).hom ≫
          Limits.Sigma.map f) =
          (Sigma.ι X' i ≫ (Sigma.reindex e.symm X).hom) ≫
            Limits.Sigma.map f := (Category.assoc _ _ _).symm
      _ = Sigma.ι X (e.symm i) ≫ Limits.Sigma.map f := by rw [hX]
      _ = f (e.symm i) ≫ Sigma.ι Y (e.symm i) := by rw [Sigma.ι_map]
      _ = f' i ≫
          (Sigma.ι Y' i ≫ (Sigma.reindex e.symm Y).hom) := by rw [hY]
      _ = (f' i ≫ Sigma.ι Y' i) ≫ (Sigma.reindex e.symm Y).hom :=
        (Category.assoc _ _ _).symm
      _ = (Sigma.ι X' i ≫ Limits.Sigma.map f') ≫
          (Sigma.reindex e.symm Y).hom := by rw [Sigma.ι_map]
      _ = Sigma.ι X' i ≫
          (Limits.Sigma.map f' ≫ (Sigma.reindex e.symm Y).hom) :=
        Category.assoc _ _ _
  let a : Arrow.mk (Limits.Sigma.map f') ≅
      Arrow.mk (Limits.Sigma.map f) :=
    Arrow.isoMk (Sigma.reindex e.symm X) (Sigma.reindex e.symm Y) hnat
  exact (realizationWeakEquivalences.arrow_mk_iso_iff a).1 hf'

private noncomputable def mapSigmaMapArrowIso
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (G : C ⥤ D) {ι : Type v} [HasCoproductsOfShape ι C]
    [HasCoproductsOfShape ι D]
    [PreservesColimitsOfShape (Discrete ι) G]
    {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) :
    Arrow.mk (G.map (Limits.Sigma.map f)) ≅
      Arrow.mk (Limits.Sigma.map fun i => G.map (f i)) := by
  let eX := PreservesCoproduct.iso G X
  let eY := PreservesCoproduct.iso G Y
  refine Arrow.isoMk eX eY ?_
  apply (cancel_epi eX.inv).mp
  apply Sigma.hom_ext
  intro i
  have hInvX : Sigma.ι (fun i => G.obj (X i)) i ≫ eX.inv =
      G.map (Sigma.ι X i) := by
    change Sigma.ι (fun i => G.obj (X i)) i ≫
      (PreservesCoproduct.iso G X).inv = _
    rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  have hY : G.map (Sigma.ι Y i) ≫ eY.hom =
      Sigma.ι (fun i => G.obj (Y i)) i := by
    apply (cancel_mono eY.inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change G.map (Sigma.ι Y i) =
      Sigma.ι (fun i => G.obj (Y i)) i ≫
        (PreservesCoproduct.iso G Y).inv
    rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  simp only [Iso.inv_hom_id_assoc]
  calc
    Sigma.ι (fun i => G.obj (X i)) i ≫
        Limits.Sigma.map (fun i => G.map (f i)) =
      G.map (f i) ≫ Sigma.ι (fun i => G.obj (Y i)) i := by
        rw [Sigma.ι_map]
    _ = G.map (f i) ≫ (G.map (Sigma.ι Y i) ≫ eY.hom) := by rw [hY]
    _ = (G.map (f i) ≫ G.map (Sigma.ι Y i)) ≫ eY.hom :=
      (Category.assoc _ _ _).symm
    _ = G.map (f i ≫ Sigma.ι Y i) ≫ eY.hom := by rw [G.map_comp]
    _ = G.map (Sigma.ι X i ≫ Limits.Sigma.map f) ≫ eY.hom := by
      rw [Sigma.ι_map]
    _ = (G.map (Sigma.ι X i) ≫ G.map (Limits.Sigma.map f)) ≫ eY.hom := by
      rw [G.map_comp]
    _ = G.map (Sigma.ι X i) ≫ G.map (Limits.Sigma.map f) ≫ eY.hom :=
      Category.assoc _ _ _
    _ = (Sigma.ι (fun i => G.obj (X i)) i ≫ eX.inv) ≫
        G.map (Limits.Sigma.map f) ≫ eY.hom := by rw [hInvX]
    _ = Sigma.ι (fun i => G.obj (X i)) i ≫ eX.inv ≫
        G.map (Limits.Sigma.map f) ≫ eY.hom := by
      simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary same-universe coproduct of realization weak equivalences is
a realization weak equivalence. -/
theorem sigma_map_mem_realizationWeakEquivalences
    {ι : Type u} {X Y : ι → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, realizationWeakEquivalences (f i)) :
    realizationWeakEquivalences (Limits.Sigma.map f) := by
  let R : SSet.{u} ⥤ SSet.{u} := SSet.toTop.{u} ⋙ TopCat.toSSet.{u}
  let RX : ι → SSet.{u} := fun i => R.obj (X i)
  let RY : ι → SSet.{u} := fun i => R.obj (Y i)
  let Rf : ∀ i, RX i ⟶ RY i := fun i => R.map (f i)
  let alphaR : Discrete.functor RX ⟶ Discrete.functor RY :=
    Discrete.natTrans fun i => Rf i.as
  let FX : Finset (Discrete ι) ⥤ SSet.{u} :=
    CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor RX)
  let FY : Finset (Discrete ι) ⥤ SSet.{u} :=
    CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor RY)
  let beta : FX ⟶ FY :=
    (CoproductsFromFiniteFiltered.liftToFinset SSet.{u} ι).map
      alphaR
  let cX : Cocone FX := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone RX
  let cY : Cocone FY := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone RY
  have hcX : IsColimit cX :=
    CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone RX
  have hcY : IsColimit cY :=
    CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone RY
  have hbeta (S : Finset (Discrete ι)) : KanComplex.W (beta.app S) := by
    let fS : ∀ s : S, X s.val.as ⟶ Y s.val.as := fun s => f s.val.as
    have hfinite : realizationWeakEquivalences (Limits.Sigma.map fS) :=
      sigma_map_mem_realizationWeakEquivalences_of_finite fS
        (fun s => hf s.val.as)
    have hmapped : KanComplex.W (R.map (Limits.Sigma.map fS)) := by
      exact hfinite
    let e := mapSigmaMapArrowIso R fS
    have hsigma : KanComplex.W
        (Limits.Sigma.map fun s : S => R.map (fS s)) :=
      (KanComplex.W.arrow_mk_iso_iff e).1 hmapped
    let eS := CoproductsFromFiniteFiltered.liftToFinsetEvaluationIso
      (C := SSet.{u}) S
    let eX := eS.app (Discrete.functor RX)
    let eY := eS.app (Discrete.functor RY)
    let eBeta : Arrow.mk (beta.app S) ≅
        Arrow.mk (Limits.Sigma.map fun s : S => R.map (f s.val.as)) := by
      refine Arrow.isoMk eX eY ?_
      change eX.hom ≫
          Limits.Sigma.map (fun s : S => alphaR.app s.val) =
        beta.app S ≫ eY.hom
      exact (eS.hom.naturality alphaR).symm
    exact (KanComplex.W.arrow_mk_iso_iff eBeta).2 (by
      simpa only [fS] using hsigma)
  let phi : (∐ RX) ⟶ (∐ RY) := Limits.Sigma.map Rf
  have hphi : ∀ S, cX.ι.app S ≫ phi = beta.app S ≫ cY.ι.app S := by
    intro S
    apply Sigma.hom_ext
    intro s
    change
      (Sigma.ι (fun x : S => RX x.val.as) s ≫
          Sigma.desc (fun x : S => Sigma.ι RX x.val.as)) ≫ phi =
        (Sigma.ι (fun x : S => RX x.val.as) s ≫
          Limits.Sigma.map (fun x : S => Rf x.val.as)) ≫
            Sigma.desc (fun x : S => Sigma.ι RY x.val.as)
    simp only [Sigma.ι_comp_desc, Sigma.ι_map, Category.assoc, phi]
  have hfiltered : KanComplex.W phi :=
    MorphismProperty.IsStableUnderColimitsOfShape.condition
      FX FY cX cY hcX hcY beta hbeta phi hphi
  let e := mapSigmaMapArrowIso R f
  change KanComplex.W (R.map (Limits.Sigma.map f))
  exact (KanComplex.W.arrow_mk_iso_iff e).2 hfiltered

/-- Realization weak equivalences of simplicial sets are stable under
arbitrary same-universe coproducts. -/
noncomputable instance
    realizationWeakEquivalences_isStableUnderCoproducts :
    realizationWeakEquivalences.{u}.IsStableUnderCoproducts.{u} where
  isStableUnderCoproductsOfShape ι :=
    IsStableUnderCoproductsOfShape.mk realizationWeakEquivalences ι
      (fun _ _ _ _ f hf => sigma_map_mem_realizationWeakEquivalences f hf)

end SSet

end
