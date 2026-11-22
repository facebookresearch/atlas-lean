/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveKanModel
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.RepresentableBoundaryCellFactorization
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarLeibnizHom
import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Original Cartesian generators and their scalar Leibniz corners

Both pushout injections are swapped by an actual tensor shuffle. The localizer factors use the one
existing native
baseline factorization; no factorization or comparison is supplied by a caller.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory HomotopicalAlgebra Opposite
open scoped MonoidalCategory Simplicial

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D]

/-- Move the scalar through the second presheaf using native associators and braiding. -/
def scalarTensorProductShuffle (T : SimplicialPresheaf.{u} D) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} D) :
    ((scalarTensor.obj T).obj K) ⊗ X ≅ (scalarTensor.obj (T ⊗ X)).obj K :=
  (α_ T ((Functor.const Dᵒᵖ).obj K) X) ≪≫
    MonoidalCategory.whiskerLeftIso T (β_ ((Functor.const Dᵒᵖ).obj K) X) ≪≫
    (α_ T X ((Functor.const Dᵒᵖ).obj K)).symm

/-- Both point formulas and all three original parameter maps are retained. -/
theorem scalarTensorProductShuffle_laws (T : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (X : SimplicialPresheaf.{u} D) :
    (∀ a n z, ((scalarTensorProductShuffle T K X).hom.app a).app n z =
      ((z.1.1, z.2), z.1.2)) ∧
    (∀ a n z, ((scalarTensorProductShuffle T K X).inv.app a).app n z =
      ((z.1.1, z.2), z.1.2)) ∧
    (∀ (L : SSet.{u}) (j : K ⟶ L),
      (((scalarTensor.obj T).map j) ▷ X) ≫ (scalarTensorProductShuffle T L X).hom =
        (scalarTensorProductShuffle T K X).hom ≫ (scalarTensor.obj (T ⊗ X)).map j) ∧
    (∀ (Y : SimplicialPresheaf.{u} D) (f : X ⟶ Y),
      (((scalarTensor.obj T).obj K) ◁ f) ≫ (scalarTensorProductShuffle T K Y).hom =
        (scalarTensorProductShuffle T K X).hom ≫ (scalarTensor.map (T ◁ f)).app K) ∧
    (∀ (T' : SimplicialPresheaf.{u} D) (t : T ⟶ T'),
      (((scalarTensor.map t).app K) ▷ X) ≫ (scalarTensorProductShuffle T' K X).hom =
        (scalarTensorProductShuffle T K X).hom ≫ (scalarTensor.map (t ▷ X)).app K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a n z
    rfl
  · intro a n z
    rfl
  · intro L j
    ext a n z
    rfl
  · intro Y f
    ext a n z
    rfl
  · intro T' t
    ext a n z
    rfl

/-- The actual Cartesian corner is the scalar corner, with its injections interchanged. -/
def scalarCartesianLeibnizIso (T : SimplicialPresheaf.{u} D)
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) :
    (Arrow.mk ((scalarTensor.obj T).map j) □ Arrow.mk f) ≅
      Arrow.mk (scalarPushoutObjObj (T ◁ f) j).ι := by
  let F := curriedTensor (SimplicialPresheaf.{u} D)
  let c := Functor.PushoutObjObj.ofHasPushout F ((scalarTensor.obj T).map j) f
  let q := scalarPushoutObjObj (T ◁ f) j
  change Arrow.mk c.ι ≅ Arrow.mk q.ι
  let eKA := scalarTensorProductShuffle T K A
  let eKB := scalarTensorProductShuffle T K B
  let eLA := scalarTensorProductShuffle T L A
  let eLB := scalarTensorProductShuffle T L B
  have hj (X : SimplicialPresheaf.{u} D) :
      (F.map ((scalarTensor.obj T).map j)).app X ≫
          (scalarTensorProductShuffle T L X).hom =
        (scalarTensorProductShuffle T K X).hom ≫ (scalarTensor.obj (T ⊗ X)).map j := by
    ext a n z
    rfl
  have hf (M : SSet.{u}) :
      (F.obj ((scalarTensor.obj T).obj M)).map f ≫
          (scalarTensorProductShuffle T M B).hom =
        (scalarTensorProductShuffle T M A).hom ≫ (scalarTensor.map (T ◁ f)).app M := by
    ext a n z
    rfl
  have hjInv (X : SimplicialPresheaf.{u} D) :
      (scalarTensor.obj (T ⊗ X)).map j ≫ (scalarTensorProductShuffle T L X).inv =
        (scalarTensorProductShuffle T K X).inv ≫
          (F.map ((scalarTensor.obj T).map j)).app X := by
    apply (cancel_mono (scalarTensorProductShuffle T L X).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hj X]
    simp
  have hfInv (M : SSet.{u}) :
      (scalarTensor.map (T ◁ f)).app M ≫ (scalarTensorProductShuffle T M B).inv =
        (scalarTensorProductShuffle T M A).inv ≫
          (F.obj ((scalarTensor.obj T).obj M)).map f := by
    apply (cancel_mono (scalarTensorProductShuffle T M B).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hf M]
    simp
  let H : c.pt ⟶ q.pt := c.isPushout.desc
    (eLA.hom ≫ q.inr) (eKB.hom ≫ q.inl) (by
      rw [← Category.assoc, hj A, Category.assoc,
        ← q.isPushout.w, ← Category.assoc, ← hf K, Category.assoc])
  let G : q.pt ⟶ c.pt := q.isPushout.desc
    (eKB.inv ≫ c.inr) (eLA.inv ≫ c.inl) (by
      rw [← Category.assoc, hfInv K, Category.assoc,
        ← c.isPushout.w, ← Category.assoc, ← hjInv A, Category.assoc])
  have hHG : H ≫ G = 𝟙 c.pt := by
    apply c.hom_ext <;> simp [H, G, Category.assoc]
  have hGH : G ≫ H = 𝟙 q.pt := by
    apply q.hom_ext <;> simp [H, G, Category.assoc]
  have hw : H ≫ q.ι = c.ι ≫ eLB.hom := by
    apply c.hom_ext
    · calc
        c.inl ≫ (H ≫ q.ι) = eLA.hom ≫ (scalarTensor.map (T ◁ f)).app L := by
          simp [H, Category.assoc]
        _ = (F.obj ((scalarTensor.obj T).obj L)).map f ≫ eLB.hom := (hf L).symm
        _ = c.inl ≫ (c.ι ≫ eLB.hom) := by simp
    · calc
        c.inr ≫ (H ≫ q.ι) = eKB.hom ≫ (scalarTensor.obj (T ⊗ B)).map j := by
          simp [H, Category.assoc]
        _ = (F.map ((scalarTensor.obj T).map j)).app B ≫ eLB.hom := (hj B).symm
        _ = c.inr ≫ (c.ι ≫ eLB.hom) := by simp
  exact Arrow.isoMk (Iso.mk H G hHG hGH) eLB hw

/-- Both source directions, both target directions and both whole Arrow squares are strict. -/
theorem scalarCartesianLeibnizIso_laws (T : SimplicialPresheaf.{u} D)
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) :
    let c := Functor.PushoutObjObj.ofHasPushout (curriedTensor (SimplicialPresheaf.{u} D))
      ((scalarTensor.obj T).map j) f
    let q := scalarPushoutObjObj (T ◁ f) j
    let e := scalarCartesianLeibnizIso T f j
    (c.inl ≫ e.hom.left = (scalarTensorProductShuffle T L A).hom ≫ q.inr) ∧
    (c.inr ≫ e.hom.left = (scalarTensorProductShuffle T K B).hom ≫ q.inl) ∧
    (q.inl ≫ e.inv.left = (scalarTensorProductShuffle T K B).inv ≫ c.inr) ∧
    (q.inr ≫ e.inv.left = (scalarTensorProductShuffle T L A).inv ≫ c.inl) ∧
    (e.hom.right = (scalarTensorProductShuffle T L B).hom) ∧
    (e.inv.right = (scalarTensorProductShuffle T L B).inv) ∧
    (e.hom.left ≫ q.ι = c.ι ≫ e.hom.right) ∧
    (e.inv.left ≫ c.ι = q.ι ≫ e.inv.right) ∧
    (e.hom ≫ e.inv = 𝟙 _) ∧ (e.inv ≫ e.hom = 𝟙 _) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · dsimp [scalarCartesianLeibnizIso, Arrow.isoMk]
    apply IsPushout.inl_desc
  · dsimp [scalarCartesianLeibnizIso, Arrow.isoMk]
    apply IsPushout.inr_desc
  · dsimp [scalarCartesianLeibnizIso, Arrow.isoMk]
    apply IsPushout.inl_desc
  · dsimp [scalarCartesianLeibnizIso, Arrow.isoMk]
    apply IsPushout.inr_desc
  · exact (scalarCartesianLeibnizIso T f j).hom.w
  · exact (scalarCartesianLeibnizIso T f j).inv.w
  · exact (scalarCartesianLeibnizIso T f j).hom_inv_id
  · exact (scalarCartesianLeibnizIso T f j).inv_hom_id

variable [Small.{u} D] [LocallySmall.{u} D]

/-- The original map's monic/Monos-RLP factor, selected from the same baseline data. -/
def originalMonicLocalizerFactor (s : Arrow (SimplicialPresheaf.{u} D)) :
    MorphismProperty.MapFactorizationData (monomorphisms (SimplicialPresheaf.{u} D))
      (monomorphisms (SimplicialPresheaf.{u} D)).rlp s.hom :=
  (InjectiveKan.data D).cofibrationFactorization.factorizationData s.hom

/-- All original factor maps retain both squares and native identity/composition equations. -/
theorem originalMonicLocalizerFactor_maps
    (s t r : Arrow (SimplicialPresheaf.{u} D)) (φ : s ⟶ t) (ψ : t ⟶ r) :
    let F := (InjectiveKan.data D).cofibrationFactorization
    ((originalMonicLocalizerFactor s).i ≫ F.Z.map φ =
      φ.left ≫ (originalMonicLocalizerFactor t).i) ∧
    (F.Z.map φ ≫ (originalMonicLocalizerFactor t).p =
      (originalMonicLocalizerFactor s).p ≫ φ.right) ∧
    (F.Z.map (𝟙 s) = 𝟙 _) ∧
    (F.Z.map (φ ≫ ψ) = F.Z.map φ ≫ F.Z.map ψ) := by
  dsimp only [originalMonicLocalizerFactor,
    MorphismProperty.FunctorialFactorizationData.factorizationData]
  exact ⟨((InjectiveKan.data D).cofibrationFactorization.i.naturality φ).symm,
    (InjectiveKan.data D).cofibrationFactorization.p.naturality φ,
    (InjectiveKan.data D).cofibrationFactorization.Z.map_id s,
    (InjectiveKan.data D).cofibrationFactorization.Z.map_comp φ ψ⟩

/-- The literal representable-boundary generator uses the same chosen monic factor. -/
def representableBoundaryMonicFactorIso {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (a : I) (d : D) (n : ℕ) :
    (Arrow.mk (representableBoundaryCell (d, n)) □
      Arrow.mk (originalMonicLocalizerFactor (S a)).i) ≅
        Arrow.mk (scalarPushoutObjObj
          (discreteYoneda.obj d ◁ (originalMonicLocalizerFactor (S a)).i)
          (SSet.boundary.{u} n).ι).ι :=
  scalarCartesianLeibnizIso (discreteYoneda.obj d)
    (originalMonicLocalizerFactor (S a)).i (SSet.boundary.{u} n).ι

/-- The original source, right factor and forward/inverse generator squares are retained. -/
theorem representableBoundaryMonicFactorIso_laws {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (a : I) (d : D) (n : ℕ) :
    let q := originalMonicLocalizerFactor (S a)
    let e := representableBoundaryMonicFactorIso S a d n
    let k := scalarPushoutObjObj (discreteYoneda.obj d ◁ q.i) (SSet.boundary.{u} n).ι
    let c := Arrow.mk (representableBoundaryCell (d, n)) □ Arrow.mk q.i
    (monomorphisms (SimplicialPresheaf.{u} D) q.i) ∧
    ((monomorphisms (SimplicialPresheaf.{u} D)).rlp q.p) ∧
    (q.i ≫ q.p = (S a).hom) ∧
    (e.hom.left ≫ k.ι = c.hom ≫ e.hom.right) ∧
    (e.inv.left ≫ c.hom = k.ι ≫ e.inv.right) ∧
    (e.hom ≫ e.inv = 𝟙 _) ∧ (e.inv ≫ e.hom = 𝟙 _) := by
  dsimp only
  refine ⟨(originalMonicLocalizerFactor (S a)).hi,
    (originalMonicLocalizerFactor (S a)).hp,
    (originalMonicLocalizerFactor (S a)).fac, ?_, ?_, ?_, ?_⟩
  · exact (representableBoundaryMonicFactorIso S a d n).hom.w
  · exact (representableBoundaryMonicFactorIso S a d n).inv.w
  · exact (representableBoundaryMonicFactorIso S a d n).hom_inv_id
  · exact (representableBoundaryMonicFactorIso S a d n).inv_hom_id

/-- The actual free-evaluation boundary is transported as a whole Arrow before the shuffle. -/
def freeBoundaryMonicFactorIso {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (a : I) (d : D) (n : ℕ) :
    (Arrow.mk ((freeEvaluationFunctor.obj d).map (SSet.boundary.{u} n).ι) □
      Arrow.mk (originalMonicLocalizerFactor (S a)).i) ≅
        Arrow.mk (scalarPushoutObjObj
          (discreteYoneda.obj d ◁ (originalMonicLocalizerFactor (S a)).i)
          (SSet.boundary.{u} n).ι).ι :=
  (MonoidalCategory.Arrow.pushoutProduct.flip.obj
      (Arrow.mk (originalMonicLocalizerFactor (S a)).i)).mapIso
      (freeScalarArrowIso d (SSet.boundary.{u} n).ι) ≪≫
    representableBoundaryMonicFactorIso S a d n

/-- All four free-image components and both resulting whole squares use the original maps. -/
theorem freeBoundaryMonicFactorIso_laws {I : Type i}
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (a : I) (d : D) (n : ℕ) :
    let q := originalMonicLocalizerFactor (S a)
    let e₀ := (MonoidalCategory.Arrow.pushoutProduct.flip.obj (Arrow.mk q.i)).mapIso
      (freeScalarArrowIso d (SSet.boundary.{u} n).ι)
    let e₁ := representableBoundaryMonicFactorIso S a d n
    let e := freeBoundaryMonicFactorIso S a d n
    let c := Arrow.mk ((freeEvaluationFunctor.obj d).map (SSet.boundary.{u} n).ι) □
      Arrow.mk q.i
    let k := scalarPushoutObjObj (discreteYoneda.obj d ◁ q.i) (SSet.boundary.{u} n).ι
    (e.hom.left = e₀.hom.left ≫ e₁.hom.left) ∧
    (e.hom.right = e₀.hom.right ≫ e₁.hom.right) ∧
    (e.inv.left = e₁.inv.left ≫ e₀.inv.left) ∧
    (e.inv.right = e₁.inv.right ≫ e₀.inv.right) ∧
    (e.hom.left ≫ k.ι = c.hom ≫ e.hom.right) ∧
    (e.inv.left ≫ c.hom = k.ι ≫ e.inv.right) ∧
    (e.hom ≫ e.inv = 𝟙 _) ∧ (e.inv ≫ e.hom = 𝟙 _) := by
  dsimp only
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact (freeBoundaryMonicFactorIso S a d n).hom.w
  · exact (freeBoundaryMonicFactorIso S a d n).inv.w
  · exact (freeBoundaryMonicFactorIso S a d n).hom_inv_id
  · exact (freeBoundaryMonicFactorIso S a d n).inv_hom_id

end SimplicialPresheaf
