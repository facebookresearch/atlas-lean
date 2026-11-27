/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Arithmetic and colimit support for join--horn decompositions

Internal support for the canonical join--horn identifications. It reuses
right-variable join naturality and isolates ordinal-sum face arithmetic, connected face
multispans, and the right-factor computation used by `JoinHorn`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor

universe u w

namespace SSet
namespace JoinHorn.Internal

/-!
## Internal connected-colimit and right-naturality tools
-/

theorem joinHorn_right_zigzag {ι : Type w} [LinearOrder ι]
    (a b : ι) :
    Zigzag (WalkingMultispan.right (J := MultispanShape.ofLinearOrder ι) a)
      (WalkingMultispan.right (J := MultispanShape.ofLinearOrder ι) b) := by
  by_cases h : a = b
  · subst b
    exact Zigzag.refl _
  rcases lt_or_gt_of_ne h with hab | hba
  · exact Zigzag.of_inv_hom
      (WalkingMultispan.Hom.fst (J := MultispanShape.ofLinearOrder ι) ⟨⟨a,b⟩,hab⟩)
      (WalkingMultispan.Hom.snd (J := MultispanShape.ofLinearOrder ι) ⟨⟨a,b⟩,hab⟩)
  · exact Zigzag.of_inv_hom
      (WalkingMultispan.Hom.snd (J := MultispanShape.ofLinearOrder ι) ⟨⟨b,a⟩,hba⟩)
      (WalkingMultispan.Hom.fst (J := MultispanShape.ofLinearOrder ι) ⟨⟨b,a⟩,hba⟩)

lemma joinHorn_isConnectedWalkingMultispan {ι : Type w} [LinearOrder ι] [Nonempty ι] :
    IsConnected (WalkingMultispan (MultispanShape.ofLinearOrder ι)) := by
  let _ : Nonempty (WalkingMultispan (MultispanShape.ofLinearOrder ι)) :=
    ⟨WalkingMultispan.right (Classical.choice (inferInstance : Nonempty ι))⟩
  apply zigzag_isConnected
  intro x y
  rcases x with x | x <;> rcases y with y | y
  · exact (Zigzag.of_hom
      (WalkingMultispan.Hom.fst (J := MultispanShape.ofLinearOrder ι) x)).trans
      ((joinHorn_right_zigzag (ι := ι) x.1.1 y.1.1).trans
        (Zigzag.of_inv
          (WalkingMultispan.Hom.fst (J := MultispanShape.ofLinearOrder ι) y)))
  · exact (Zigzag.of_hom
      (WalkingMultispan.Hom.fst (J := MultispanShape.ofLinearOrder ι) x)).trans
      (joinHorn_right_zigzag (ι := ι) x.1.1 y)
  · exact (joinHorn_right_zigzag (ι := ι) x y.1.1).trans
      (Zigzag.of_inv
        (WalkingMultispan.Hom.fst (J := MultispanShape.ofLinearOrder ι) y))
  · exact joinHorn_right_zigzag (ι := ι) x y



/-- The right-block index obtained by removing the left block from a face of a
positive-dimensional join. -/
def joinBackIndexSucc
    (p q : ℕ) (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : ¬ t.val ≤ p + 1) : Fin (q + 2) :=
  ⟨t.val - (p + 2), by
    apply (Nat.sub_lt_iff_lt_add' (by omega : p + 2 ≤ t.val)).2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using t.isLt⟩

@[simp]
lemma joinBackIndexSucc_val
    (p q : ℕ) (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (ht : ¬ t.val ≤ p + 1) :
    (joinBackIndexSucc p q t ht).val = t.val - (p + 2) :=
  rfl


/-- The front inclusion commutes past a back face: `inl'` followed by
`δ ⟨K+1+a⟩` is `inl'` one dimension up. (Fin-risk R-a: front block.) -/
lemma joinHorn_inl'_comp_δ_back {K n : ℕ} (a : Fin (n + 2)) :
    AugmentedSimplexCategory.inl' ⦋K⦌ ⦋n⦌ ≫
        SimplexCategory.δ
          (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + n + 3)) =
      AugmentedSimplexCategory.inl' ⦋K⦌ ⦋n + 1⦌ := by
  ext i : 3
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  rw [AugmentedSimplexCategory.inl'_eval, AugmentedSimplexCategory.inl'_eval]
  have hval : ∀ (t : Fin (K + n + 2)),
      (SimplexCategory.δ
        (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + n + 3))).toOrderHom
        t =
      Fin.succAbove (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + n + 3)) t :=
    fun t => rfl
  rw [hval]
  apply Fin.ext
  rw [Fin.succAbove_of_castSucc_lt]
  · simp [Fin.castAdd, Fin.cast]
  · rw [Fin.lt_def]
    simp only [Fin.val_castSucc, Fin.val_cast,
      Fin.val_castAdd]
    have hi := i.is_lt
    have ha := a.is_lt
    simp only [Fin.is_lt] at hi ha ⊢
    omega

/-- The back-face formula for `inr'`: pushing a back face past the back
inclusion. (Fin-risk R-a: back block, case split.) -/
lemma joinHorn_inr'_comp_δ_back {K n : ℕ} (a : Fin (n + 2)) :
    AugmentedSimplexCategory.inr' ⦋K⦌ ⦋n⦌ ≫
        SimplexCategory.δ
          (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + n + 3)) =
      SimplexCategory.δ a ≫ AugmentedSimplexCategory.inr' ⦋K⦌ ⦋n + 1⦌ := by
  ext i : 3
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  rw [AugmentedSimplexCategory.inr'_eval, AugmentedSimplexCategory.inr'_eval]
  have hδ : ∀ {N : ℕ} (p : Fin (N + 2)) (t : Fin (N + 1)),
      (SimplexCategory.δ p).toOrderHom t = Fin.succAbove p t :=
    fun p t => rfl
  rw [hδ, hδ]
  by_cases h : i.val < a.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc, Fin.val_cast, Fin.val_natAdd]
      have ha := a.is_lt
      simp only [Fin.is_lt] at ha ⊢
      omega)]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc]
      exact h)]
    apply Fin.ext
    simp [Fin.natAdd, Fin.cast]
  · push Not at h
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      rw [Fin.le_def]
      simp only [Fin.val_castSucc, Fin.val_cast, Fin.val_natAdd]
      have ha := a.is_lt
      simp only [Fin.is_lt] at ha ⊢
      omega)]
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      rw [Fin.le_def]
      simp only [Fin.val_castSucc]
      exact h)]
    apply Fin.ext
    simp [Fin.natAdd, Fin.cast]
    omega

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Tensoring a face map with the identity on `⦋K⦌` on the left is the
back face map `δ ⟨K+1+a⟩`, in the augmented simplex category. Proof by
`tensorObj_hom_ext` (mirror of `SSet.ofHom_δ_tensorHom_id`). -/
lemma joinHorn_ofHom_id_tensorHom_δ {K n : ℕ} (a : Fin (n + 2)) :
    (𝟙 (WithInitial.of ⦋K⦌) ⊗ₘ
        Join.ofHom (SimplexCategory.δ a)) =
      Join.ofHom (SimplexCategory.δ
        (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + n + 3))) := by
  apply AugmentedSimplexCategory.tensorObj_hom_ext
  · rw [AugmentedSimplexCategory.inl_comp_tensorHom, Category.id_comp]
    exact (joinHorn_inl'_comp_δ_back a).symm
  · rw [AugmentedSimplexCategory.inr_comp_tensorHom]
    exact (joinHorn_inr'_comp_δ_back a).symm

/-- `SSet.ofHom_id_tensorHom_δ` read in `SimplexCategory`. -/
lemma joinHorn_tensorHomOf_id_δ {K n : ℕ} (a : Fin (n + 2)) :
    AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋K⦌)
        (SimplexCategory.δ a) =
      SimplexCategory.δ
        (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + n + 3)) :=
  congrArg WithInitial.down (joinHorn_ofHom_id_tensorHom_δ a)



/-- Reindexing iso for standard simplices along a dimension identity. -/
def joinHornΔcastIso {A B : ℕ} (h : A = B) : (Δ[A] : SSet.{u}) ≅ Δ[B] :=
  SSet.stdSimplex.mapIso (eqToIso (by rw [h] : ⦋A⦌ = ⦋B⦌))

/-- Reindexing cast for standard simplices along a dimension identity. -/
def joinHornΔcast {A B : ℕ} (h : A = B) : (Δ[A] : SSet.{u}) ⟶ Δ[B] :=
  (joinHornΔcastIso h).hom

instance joinHornΔcast_isIso {A B : ℕ} (h : A = B) :
    IsIso (joinHornΔcast.{u} h) := by
  unfold joinHornΔcast
  infer_instance

/-- The inverse cast. -/
def joinHornΔcastInv {A B : ℕ} (h : A = B) : (Δ[B] : SSet.{u}) ⟶ Δ[A] :=
  (joinHornΔcastIso h).inv

lemma joinHornΔcastInv_eq {A B : ℕ} (h : A = B) :
    joinHornΔcastInv h = joinHornΔcast h.symm := by
  subst B
  simp [joinHornΔcastInv, joinHornΔcast, joinHornΔcastIso]

/-- Casts compose. -/
@[reassoc]
lemma joinHornΔcast_comp {A B C : ℕ} (h₁ : A = B) (h₂ : B = C) :
    joinHornΔcast h₁ ≫ joinHornΔcast h₂ = joinHornΔcast (h₁.trans h₂) := by
  unfold joinHornΔcast joinHornΔcastIso
  rw [← Iso.trans_hom, ← Functor.mapIso_trans, eqToIso_trans]

/-- Casts between the same objects agree. -/
lemma joinHornΔcast_eq {A B : ℕ} (h h' : A = B) : joinHornΔcast h = joinHornΔcast h' := by
  have e : h = h' := proof_irrel _ _
  rw [e]

/-- Cancellation for casts (they are isomorphisms). -/
lemma joinHornΔcast_cancel {A B : ℕ} (h : A = B) {X : SSet.{u}}
    {a b : (Δ[B] : SSet.{u}) ⟶ X} (e : joinHornΔcast h ≫ a = joinHornΔcast h ≫ b) :
    a = b := by
  have h1 : joinHornΔcastInv h ≫ joinHornΔcast h = 𝟙 _ := (joinHornΔcastIso h).inv_hom_id
  calc a = 𝟙 _ ≫ a := by rw [Category.id_comp]
    _ = (joinHornΔcastInv h ≫ joinHornΔcast h) ≫ a := by rw [h1]
    _ = joinHornΔcastInv h ≫ (joinHornΔcast h ≫ a) := by rw [Category.assoc]
    _ = joinHornΔcastInv h ≫ (joinHornΔcast h ≫ b) := by rw [e]
    _ = (joinHornΔcastInv h ≫ joinHornΔcast h) ≫ b := by rw [Category.assoc]
    _ = 𝟙 _ ≫ b := by rw [h1]
    _ = b := by rw [Category.id_comp]


/-- Faces push through casts (same vertex, possibly different spelling):
`δ a ≫ joinHornΔcast h = joinHornΔcast h' ≫ δ a'`. -/
lemma joinHorn_δ_joinHornΔcast {A B : ℕ} (h : A + 1 = B + 1) (h' : A = B)
    (a : Fin (A + 2)) (a' : Fin (B + 2)) (ha : a.val = a'.val) :
    stdSimplex.δ a ≫ joinHornΔcast h = joinHornΔcast h' ≫ stdSimplex.δ a' := by
  rw [stdSimplex_δ_eq_map, stdSimplex_δ_eq_map]
  simp only [joinHornΔcast, joinHornΔcastIso, Functor.mapIso_hom, ← Functor.map_comp]
  congr 1
  have hδ : ∀ {N : ℕ} (p : Fin (N + 2)) (t : Fin (N + 1)),
      (SimplexCategory.δ p).toOrderHom t = Fin.succAbove p t :=
    fun p t => rfl
  have hcast : ∀ {P Q : ℕ} (e : P = Q) (s : Fin P),
      (Fin.castOrderIso e).toOrderEmbedding.toOrderHom s = Fin.cast e s :=
    fun e s => rfl
  have heq : ∀ {P Q : SimplexCategory} (e : P = Q),
      (eqToIso e).hom = eqToHom e := fun e => rfl
  ext t
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, heq, SimplexCategory.eqToHom_toOrderHom, hδ, hcast]
  simp only [Fin.val_cast]
  by_cases hta : t.val < a.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc]
      exact hta)]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc, Fin.val_cast]
      omega)]
    simp only [Fin.val_castSucc, Fin.val_cast]
  · push Not at hta
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      rw [Fin.le_def]
      simp only [Fin.val_castSucc]
      exact hta)]
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      rw [Fin.le_def]
      simp only [Fin.val_castSucc, Fin.val_cast]
      omega)]
    simp only [Fin.val_succ, Fin.val_cast]

/-!
### G6b. Pushing faces through `SSet.joinStdSimplexIso`

Front faces (`k = 0` and general) and back faces, pushed through
`joinStdSimplexIso.inv`. The general front push needs only Mathlib
naturality plus order-hom computations (no `tensorHomOf` equations,
which are definitionally blocked for front faces).
-/


/-- The right-block inclusion used by the zero-left-face computation. -/
def joinHornBackInclusionStd (K n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[K + n + 1] :=
  SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋K⦌ ⦋n⦌)

/-- Pushing the vertex face through the `0`-iso: omitting the front
vertex is the back inclusion (up to the `0 + m = m` cast). -/
@[reassoc]
lemma joinHorn_frontPush_zero {m : ℕ} (a0 : Fin (0 + m + 2)) (ha0 : a0.val = 0) :
    stdSimplex.δ a0 ≫ (SSet.joinStdSimplexIso 0 m).inv =
      joinHornΔcast (by omega : 0 + m = m) ≫
        SSet.joinInr (Δ[0] : SSet.{u}) (Δ[m] : SSet.{u}) := by
  have hback : SSet.joinInr (Δ[0] : SSet.{u}) (Δ[m] : SSet.{u}) ≫
      (SSet.joinStdSimplexIso 0 m).hom = joinHornBackInclusionStd 0 m := by
    rw [joinHornBackInclusionStd, joinInr_comp_joinStdSimplexIso_hom]
  have key : (stdSimplex.δ a0 ≫ (SSet.joinStdSimplexIso 0 m).inv) ≫
      (SSet.joinStdSimplexIso 0 m).hom =
      (joinHornΔcast (by omega : 0 + m = m) ≫ SSet.joinInr _ _) ≫
        (SSet.joinStdSimplexIso 0 m).hom := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      hback]
    rw [joinHornBackInclusionStd, stdSimplex_δ_eq_map, joinHornΔcast, joinHornΔcastIso,
      Functor.mapIso_hom, ← Functor.map_comp]
    congr 1
    have hδ : ∀ {N : ℕ} (p : Fin (N + 2)) (t : Fin (N + 1)),
        (SimplexCategory.δ p).toOrderHom t = Fin.succAbove p t :=
      fun p t => rfl
    have hcast : ∀ {P Q : ℕ} (e : P = Q) (s : Fin P),
        (Fin.castOrderIso e).toOrderEmbedding.toOrderHom s = Fin.cast e s :=
      fun e s => rfl
    have heq : ∀ {P Q : SimplexCategory} (e : P = Q),
        (eqToIso e).hom = eqToHom e := fun e => rfl
    have hinr : ∀ (s : Fin (m + 1)),
        (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom s =
          (s.natAdd (0 + 1)).cast (Nat.succ_add 0 (m + 1)) := by
      intro s
      have e := AugmentedSimplexCategory.inr'_eval ⦋0⦌ ⦋m⦌ s
      simpa [SimplexCategory.len_mk] using e
    ext t
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply, heq, SimplexCategory.eqToHom_toOrderHom, hδ,
      hcast, hinr]
    simp only [Fin.val_cast, Fin.val_natAdd]
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      rw [Fin.le_def]
      simp only [Fin.val_castSucc]
      omega)]
    simp only [Fin.val_succ]
    omega
  calc stdSimplex.δ a0 ≫ (SSet.joinStdSimplexIso 0 m).inv
      = ((stdSimplex.δ a0 ≫ (SSet.joinStdSimplexIso 0 m).inv) ≫
          (SSet.joinStdSimplexIso 0 m).hom) ≫
          (SSet.joinStdSimplexIso 0 m).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = ((joinHornΔcast (by omega : 0 + m = m) ≫ SSet.joinInr _ _) ≫
          (SSet.joinStdSimplexIso 0 m).hom) ≫
          (SSet.joinStdSimplexIso 0 m).inv := by rw [key]
    _ = joinHornΔcast (by omega : 0 + m = m) ≫ SSet.joinInr _ _ := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]


/-- Pushing a front face through the join iso: `δ` of a front vertex
is a cast followed by the face join. The proof computes
`tensorHomOf` at the order-hom level (its equation form is
definitionally blocked for front faces). -/
@[reassoc]
lemma joinHorn_frontPush {k' m : ℕ} (r : Fin (k' + 2))
    (a : Fin ((k' + 1) + m + 2)) (ha : a.val = r.val) :
    stdSimplex.δ a ≫ (SSet.joinStdSimplexIso (k' + 1) m).inv =
      joinHornΔcast (by omega : (k' + 1) + m = k' + m + 1) ≫
        (SSet.joinStdSimplexIso k' m).inv ≫
          (SSet.join.map (stdSimplex.δ r)).app (Δ[m] : SSet.{u}) := by
  have hnat :=
    SSet.joinStdSimplexIso_natural_left (n := m) (SimplexCategory.δ r)
  have hinv {Y : SSet.{u}} (Z : (Δ[k' + m + 1] : SSet.{u}) ⟶ Y) :
      (SSet.joinStdSimplexIso k' m).inv ≫
        ((SSet.joinStdSimplexIso k' m).hom ≫ Z) = Z := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have key : (stdSimplex.δ a ≫ (SSet.joinStdSimplexIso (k' + 1) m).inv) ≫
      (SSet.joinStdSimplexIso (k' + 1) m).hom =
      (joinHornΔcast (by omega : (k' + 1) + m = k' + m + 1) ≫
        (SSet.joinStdSimplexIso k' m).inv ≫
          (SSet.join.map (stdSimplex.δ r)).app (Δ[m] : SSet.{u})) ≫
        (SSet.joinStdSimplexIso (k' + 1) m).hom := by
    simp only [Category.assoc]
    rw [Iso.inv_hom_id, Category.comp_id, stdSimplex_δ_eq_map r, hnat,
      hinv]
    rw [stdSimplex_δ_eq_map, joinHornΔcast, joinHornΔcastIso, Functor.mapIso_hom,
      ← Functor.map_comp]
    congr 1
    have hδ : ∀ {N : ℕ} (p : Fin (N + 2)) (t : Fin (N + 1)),
        (SimplexCategory.δ p).toOrderHom t = Fin.succAbove p t :=
      fun p t => rfl
    have hcast : ∀ {P Q : ℕ} (e : P = Q) (s : Fin P),
        (Fin.castOrderIso e).toOrderEmbedding.toOrderHom s = Fin.cast e s :=
      fun e s => rfl
    have heq : ∀ {P Q : SimplexCategory} (e : P = Q),
        (eqToIso e).hom = eqToHom e := fun e => rfl
    ext t
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply, heq, SimplexCategory.eqToHom_toOrderHom, hδ,
      hcast]
    dsimp only [AugmentedSimplexCategory.tensorHomOf,
      SimplexCategory.mkHom]
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply, SimplexCategory.eqToHom_toOrderHom, hcast,
      SimplexCategory.len_mk, SimplexCategory.Hom.toOrderHom_mk,
      Fin.val_cast]
    suffices key : ∀ (s : Fin ((k' + 1) + (m + 1))) (_ : s.val = t.val),
        (a.succAbove t).val = (Fin.addCases (m := k' + 1) (n := m + 1)
          (motive := fun _ ↦ Fin ((k' + 2) + (m + 1)))
          (fun i ↦ Fin.castAdd (m + 1)
            ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ r)) i))
          (fun i ↦ Fin.natAdd (k' + 1 + 1)
            ((SimplexCategory.Hom.toOrderHom (𝟙 ⦋m⦌)) i)) s).val by
      exact key _ (by simp only [Fin.val_cast])
    intro s hs
    revert hs
    refine Fin.addCases (fun u hsu => ?_) (fun v hsv => ?_) s
    · rw [Fin.addCases_left]
      have hu : u.val = t.val := by
        have h2 := hsu
        simp only [Fin.val_castAdd] at h2
        exact h2
      simp only [Fin.val_castAdd, hδ]
      by_cases htu : t.val < r.val
      · have h1 : Fin.castSucc u < r := by
          rw [Fin.lt_def]
          simp only [Fin.val_castSucc]
          omega
        have h2 : Fin.castSucc t < a := by
          rw [Fin.lt_def]
          simp only [Fin.val_castSucc]
          omega
        rw [Fin.succAbove_of_castSucc_lt _ _ h1,
          Fin.succAbove_of_castSucc_lt _ _ h2]
        simp only [Fin.val_castSucc]
        omega
      · push Not at htu
        have h1 : r ≤ Fin.castSucc u := by
          rw [Fin.le_def]
          simp only [Fin.val_castSucc]
          omega
        have h2 : a ≤ Fin.castSucc t := by
          rw [Fin.le_def]
          simp only [Fin.val_castSucc]
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ h1,
          Fin.succAbove_of_le_castSucc _ _ h2]
        simp only [Fin.val_succ]
        omega
    · rw [Fin.addCases_right]
      have hv : (k' + 1) + v.val = t.val := by
        have h2 := hsv
        simp only [Fin.val_natAdd] at h2
        omega
      have h1id : (SimplexCategory.Hom.toOrderHom (𝟙 ⦋m⦌)) v = v := rfl
      simp only [Fin.val_natAdd, h1id]
      have hta : ¬ t.val < a.val := by omega
      rw [Fin.succAbove_of_le_castSucc _ _ (by
        rw [Fin.le_def]
        simp only [Fin.val_castSucc]
        omega)]
      simp only [Fin.val_succ]
      omega
  calc stdSimplex.δ a ≫ (SSet.joinStdSimplexIso (k' + 1) m).inv
      = ((stdSimplex.δ a ≫ (SSet.joinStdSimplexIso (k' + 1) m).inv) ≫
          (SSet.joinStdSimplexIso (k' + 1) m).hom) ≫
          (SSet.joinStdSimplexIso (k' + 1) m).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = ((joinHornΔcast (by omega : (k' + 1) + m = k' + m + 1) ≫
          (SSet.joinStdSimplexIso k' m).inv ≫
            (SSet.join.map (stdSimplex.δ r)).app (Δ[m] : SSet.{u})) ≫
          (SSet.joinStdSimplexIso (k' + 1) m).hom) ≫
          (SSet.joinStdSimplexIso (k' + 1) m).inv := by rw [key]
    _ = joinHornΔcast (by omega : (k' + 1) + m = k' + m + 1) ≫
          (SSet.joinStdSimplexIso k' m).inv ≫
            (SSet.join.map (stdSimplex.δ r)).app (Δ[m] : SSet.{u}) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]


/-- Casts along `rfl` are identities. -/
lemma joinHornΔcast_rfl {A : ℕ} : joinHornΔcast (rfl : A = A) = 𝟙 _ := by
  have h : ∀ (p : (⦋A⦌ : SimplexCategory) = ⦋A⦌),
      (SSet.stdSimplex.mapIso (eqToIso p)).hom = 𝟙 _ := by
    intro p
    rw [proof_irrel p rfl]
    simp
  unfold joinHornΔcast joinHornΔcastIso
  exact h _

/-- Roundtrip casts are the identity. -/
lemma joinHornΔcast_comp_eq_id {A B : ℕ} (h : A = B) (h' : B = A) :
    joinHornΔcast h ≫ joinHornΔcast h' = 𝟙 _ := by
  rw [joinHornΔcast_comp, joinHornΔcast_eq _ rfl, joinHornΔcast_rfl]

/-- Pushing a back-block face through the standard join isomorphism. -/
@[reassoc]
lemma joinHorn_backPush {K q : ℕ} (a : Fin (q + 2)) :
    stdSimplex.δ
        (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + q + 3)) ≫
      (SSet.joinStdSimplexIso K (q + 1)).inv =
    (SSet.joinStdSimplexIso K q).inv ≫
      (SSet.join.obj (Δ[K] : SSet.{u})).map (stdSimplex.δ a) := by
  have hnat :=
    joinStdSimplexIso_natural_right (m := K) (SimplexCategory.δ a)
  simp only [joinHorn_tensorHomOf_id_δ, ← SSet.stdSimplex_δ_eq_map] at hnat
  have key : (stdSimplex.δ
        (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + q + 3)) ≫
        (SSet.joinStdSimplexIso K (q + 1)).inv) ≫
      (SSet.joinStdSimplexIso K (q + 1)).hom =
      ((SSet.joinStdSimplexIso K q).inv ≫
        (SSet.join.obj _).map (stdSimplex.δ a)) ≫
        (SSet.joinStdSimplexIso K (q + 1)).hom := by
    simp only [Category.assoc]
    rw [Iso.inv_hom_id, Category.comp_id, hnat, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  calc stdSimplex.δ
          (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ : Fin (K + q + 3)) ≫
        (SSet.joinStdSimplexIso K (q + 1)).inv
      = ((stdSimplex.δ
            (⟨K + 1 + a.val, by have h := a.is_lt; omega⟩ :
              Fin (K + q + 3)) ≫
          (SSet.joinStdSimplexIso K (q + 1)).inv) ≫
          (SSet.joinStdSimplexIso K (q + 1)).hom) ≫
          (SSet.joinStdSimplexIso K (q + 1)).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (((SSet.joinStdSimplexIso K q).inv ≫
            (SSet.join.obj _).map (stdSimplex.δ a)) ≫
          (SSet.joinStdSimplexIso K (q + 1)).hom) ≫
          (SSet.joinStdSimplexIso K (q + 1)).inv := by rw [key]
    _ = (SSet.joinStdSimplexIso K q).inv ≫
          (SSet.join.obj _).map (stdSimplex.δ a) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Dual front push: a face join followed by the join iso is the
transported front face (up to a reindexing cast). From `joinHorn_frontPush`
by iso cancellation. -/
@[reassoc]
lemma joinHorn_dualFrontPush {k' m : ℕ} (r : Fin (k' + 2))
    (a : Fin ((k' + 1) + m + 2)) (ha : a.val = r.val)
    (h' : k' + m + 1 = (k' + 1) + m) :
    (SSet.join.map (stdSimplex.δ r)).app (Δ[m] : SSet.{u}) ≫
      (SSet.joinStdSimplexIso (k' + 1) m).hom =
    (SSet.joinStdSimplexIso k' m).hom ≫
      joinHornΔcast h' ≫ stdSimplex.δ a := by
  have hfp := joinHorn_frontPush r a ha
  have hcast : (k' + 1) + m = k' + m + 1 := by omega
  have key : ((SSet.join.map (stdSimplex.δ r)).app _ ≫
      (SSet.joinStdSimplexIso (k' + 1) m).hom) ≫
      (SSet.joinStdSimplexIso (k' + 1) m).inv =
      ((SSet.joinStdSimplexIso k' m).hom ≫
        joinHornΔcast h' ≫ stdSimplex.δ a) ≫
        (SSet.joinStdSimplexIso (k' + 1) m).inv := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hfp, joinHornΔcast_eq _ hcast, ← Category.assoc (joinHornΔcast h'),
      joinHornΔcast_comp_eq_id, Category.id_comp, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  calc (SSet.join.map (stdSimplex.δ r)).app _ ≫
        (SSet.joinStdSimplexIso (k' + 1) m).hom
      = (((SSet.join.map (stdSimplex.δ r)).app _ ≫
            (SSet.joinStdSimplexIso (k' + 1) m).hom) ≫
          (SSet.joinStdSimplexIso (k' + 1) m).inv) ≫
          (SSet.joinStdSimplexIso (k' + 1) m).hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (((SSet.joinStdSimplexIso k' m).hom ≫
              joinHornΔcast h' ≫ stdSimplex.δ a) ≫
            (SSet.joinStdSimplexIso (k' + 1) m).inv) ≫
            (SSet.joinStdSimplexIso (k' + 1) m).hom := by rw [key]
    _ = (SSet.joinStdSimplexIso k' m).hom ≫
          joinHornΔcast h' ≫ stdSimplex.δ a := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]




/-- Dual back-face transport through the standard join isomorphism. -/
lemma joinHorn_dualBackPush {K q : ℕ} (r : Fin (q + 2))
    (a : Fin (K + (q + 1) + 2)) (ha : a.val = K + 1 + r.val)
    (h' : K + q + 1 = K + (q + 1)) :
    (SSet.join.obj (Δ[K] : SSet.{u})).map (stdSimplex.δ r) ≫
        (SSet.joinStdSimplexIso K (q + 1)).hom =
      (SSet.joinStdSimplexIso K q).hom ≫
        joinHornΔcast h' ≫ stdSimplex.δ a := by
  have hnat := joinStdSimplexIso_natural_right
    (m := K) (SimplexCategory.δ r)
  simp only [joinHorn_tensorHomOf_id_δ, ← SSet.stdSimplex_δ_eq_map] at hnat
  rw [hnat]
  congr 1
  have hc := joinHorn_δ_joinHornΔcast
    (by omega : (K + q + 1) + 1 = (K + (q + 1)) + 1)
    h'
    (⟨K + 1 + r.val, by have := r.isLt; omega⟩ : Fin (K + q + 3))
    a ha.symm
  simpa only [joinHornΔcast_eq _ rfl, joinHornΔcast_rfl,
    Category.comp_id] using hc

/-- The unique back face when the right simplex is zero-dimensional. -/
@[reassoc]
lemma joinHorn_backPush_zero (K : ℕ) :
    stdSimplex.δ (Fin.last (K + 1)) ≫
        (joinStdSimplexIso K 0).inv =
      joinInl (Δ[K] : SSet.{u}) (Δ[0] : SSet.{u}) := by
  rw [← cancel_mono (joinStdSimplexIso K 0).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [joinInl_comp_joinStdSimplexIso_hom, inl'_eq_δ_last,
    ← stdSimplex_δ_eq_map]

end JoinHorn.Internal
end SSet
