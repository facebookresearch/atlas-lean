/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialSet/KanComplex/SimplicialGroup/Basic.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Simplicial groups are Kan complexes

A simplicial set whose sets of simplices are groups, with all simplicial operators group
homomorphisms, is a Kan complex (`SSet.kanComplex_of_group`, Moore's theorem). Hence the
underlying simplicial set of a simplicial group, of a simplicial abelian group and of a
simplicial module is a Kan complex.

This is what makes the combinatorial homotopy theory of simplicial groups available, and it is
the Kan property of the mapping spaces of simplicial categories built from simplicial abelian
groups, such as the Dold–Kan images of connective chain complexes.

## Proof

By `SSet.KanComplex.iff`, a horn `Λ[n + 1, i] ⟶ X` is a compatible family of `n`-simplices
`y j`, one for each face `j ≠ i`. The filler is built by correcting faces one at a time. Below
`i`, from the bottom up: if `w` already has the faces `y j` for `j < r`, then
`w * σ r ((d r w)⁻¹ * y r)` also has the face `y r`, since the correction is the degeneracy of a
simplex whose faces below `r` are trivial by compatibility. Above `i`, from the top down: if
`w` has the faces `y j` for `j < i` and `j > r`, then `w * σ (r - 1) ((d r w)⁻¹ * y r)` also has
the face `y r`, by the same argument.

## Main results

* `SSet.kanComplex_of_group`, `SSet.kanComplex_of_addGroup`: Moore's theorem for simplicial
  sets with group and with additive group structures.
* `CategoryTheory.SimplicialObject.kanComplex_comp_forget_grpCat`,
  `CategoryTheory.SimplicialObject.kanComplex_comp_forget_addCommGrpCat` and
  `CategoryTheory.SimplicialObject.kanComplex_comp_forget_moduleCat`: the underlying simplicial
  sets of simplicial groups, simplicial abelian groups and simplicial modules are Kan complexes.

## References

* J. C. Moore, *Homotopie des complexes monoïdaux, I*, Séminaire Henri Cartan 7 (1954–1955).
* J. P. May, *Simplicial Objects in Algebraic Topology*, Theorem 17.1.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Lemma I.3.4.
-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet

section Group

variable {X : SSet.{u}} [∀ n, Group (X.obj n)]
  (hX : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x y : X.obj m),
    X.map f (x * y) = X.map f x * X.map f y)

include hX

private lemma δ_mul {n : ℕ} (j : Fin (n + 2)) (x y : X _⦋n + 1⦌) :
    X.δ j (x * y) = X.δ j x * X.δ j y :=
  hX _ x y

private lemma δ_inv {n : ℕ} (j : Fin (n + 2)) (x : X _⦋n + 1⦌) : X.δ j x⁻¹ = (X.δ j x)⁻¹ :=
  map_inv (MonoidHom.mk' (fun x => X.δ j x) (δ_mul hX j)) x

private lemma σ_one {n : ℕ} (j : Fin (n + 1)) : X.σ j (1 : X _⦋n⦌) = 1 :=
  map_one (MonoidHom.mk' (fun x => X.σ j x) (hX _))

/-- Multiplying `w` by the degeneracy `σ b ((δ k w)⁻¹ * v)` does not change its `a`-th face,
when `δ a` turns `σ b` into `σ b'` after the face `δ a'`, and `δ k w` and `v` have the same
`a'`-th face. -/
private lemma δ_mul_σ_inv_mul {n : ℕ} {a k : Fin (n + 3)} {b a' : Fin (n + 2)} {b' : Fin (n + 1)}
    (hσ : ∀ x : X _⦋n + 1⦌, X.δ a (X.σ b x) = X.σ b' (X.δ a' x)) {w : X _⦋n + 2⦌}
    {v : X _⦋n + 1⦌} (hv : X.δ a' (X.δ k w) = X.δ a' v) :
    X.δ a (w * X.σ b ((X.δ k w)⁻¹ * v)) = X.δ a w := by
  simp [δ_mul hX, δ_inv hX, hσ, hv, σ_one hX]

variable {m : ℕ} {i : Fin (m + 3)} {y : ∀ j : Fin (m + 3), j ≠ i → X _⦋m + 1⦌}
  (hy : ∀ (j k : Fin (m + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
    X.δ (k.pred (Fin.ne_zero_of_lt hjk)) (y j hj) =
      X.δ (j.castPred (Fin.ne_last_of_lt hjk)) (y k hk))

include hy

/-- Correcting the face `b.castSucc < i` by multiplying with a degenerate simplex keeps the faces
below it. -/
private lemma exists_lower_step (b : Fin (m + 2)) (hbi : b.castSucc ≠ i)
    (w : X _⦋m + 2⦌) (hw : ∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < b.val → X.δ j w = y j hj) :
    ∃ w' : X _⦋m + 2⦌, ∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val ≤ b.val → X.δ j w' = y j hj := by
  refine ⟨w * X.σ b ((X.δ b.castSucc w)⁻¹ * y b.castSucc hbi), fun j hj hjb => ?_⟩
  rcases lt_or_eq_of_le hjb with hjb | hjb
  · -- Below `b`, the correction is the degeneracy of a simplex with trivial `j`-th face.
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_of_val_ne (by simp; omega) : j ≠ _)
    obtain ⟨b, rfl⟩ := Fin.exists_succ_eq.mpr
      (Fin.ne_of_val_ne (by rw [Fin.val_zero]; simp at hjb; omega) : b ≠ 0)
    have hjb' : j ≤ b.castSucc := Fin.le_def.mpr (by simp at hjb ⊢; omega)
    rw [δ_mul_σ_inv_mul hX (δ_comp_σ_of_le_apply hjb') ?_, hw _ hj hjb]
    refine (δ_comp_δ_apply hjb' w).trans ?_
    rw [hw _ hj hjb]
    simpa using hy _ _ hj hbi (Fin.lt_def.mpr (by simpa using hjb))
  · obtain rfl : j = b.castSucc := Fin.ext hjb
    rw [δ_mul hX, δ_comp_σ_self_apply, mul_inv_cancel_left]

/-- Correcting the face `b.succ > i` by multiplying with a degenerate simplex keeps the faces
below `i` and above `b.succ`. -/
private lemma exists_upper_step (b : Fin (m + 2)) (hbi : b.succ ≠ i) (hb : i.val ≤ b.val)
    (w : X _⦋m + 2⦌) (hlow : ∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < i.val → X.δ j w = y j hj)
    (hup : ∀ (j : Fin (m + 3)) (hj : j ≠ i), b.val + 1 < j.val → X.δ j w = y j hj) :
    ∃ w' : X _⦋m + 2⦌, (∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < i.val → X.δ j w' = y j hj) ∧
      ∀ (j : Fin (m + 3)) (hj : j ≠ i), b.val < j.val → X.δ j w' = y j hj := by
  refine ⟨w * X.σ b ((X.δ b.succ w)⁻¹ * y b.succ hbi), fun j hj hji => ?_, fun j hj hbj => ?_⟩
  · -- Below `i`, the correction is the degeneracy of a simplex with trivial `j`-th face.
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_of_val_ne (by simp; omega) : j ≠ _)
    obtain ⟨b, rfl⟩ := Fin.exists_succ_eq.mpr
      (Fin.ne_of_val_ne (by rw [Fin.val_zero]; simp at hji; omega) : b ≠ 0)
    have hjb : j ≤ b.castSucc := Fin.le_def.mpr (by simp at hji hb ⊢; omega)
    rw [δ_mul_σ_inv_mul hX (δ_comp_σ_of_le_apply hjb) ?_, hlow _ hj hji]
    rw [δ_comp_δ_apply (Fin.le_def.mpr (by simp at hji hb ⊢; omega)), hlow _ hj hji]
    simpa using hy _ _ hj hbi (Fin.lt_def.mpr (by simp at hji hb ⊢; omega))
  · rcases lt_or_eq_of_le (Nat.succ_le_of_lt hbj) with hbj | hbj
    · -- Above `b.succ`, the correction is the degeneracy of a simplex with trivial face.
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr
        (Fin.ne_of_val_ne (by rw [Fin.val_zero]; omega) : j ≠ 0)
      obtain ⟨b, rfl⟩ := Fin.exists_castSucc_eq.mpr
        (Fin.ne_of_val_ne (by rw [Fin.val_last]; simp at hbj; omega) : b ≠ _)
      have hbj' : b.val < j.val := by simpa using hbj
      rw [δ_mul_σ_inv_mul hX (δ_comp_σ_of_gt_apply (Fin.lt_def.mpr hbj')) ?_,
        hup j.succ hj (by simp; omega)]
      -- `δ_comp_δ_apply` names the face `b.castSucc.succ` as `b.succ.castSucc`.
      have hδ := δ_comp_δ_apply (S := X) (i := b.succ) (j := j) (Fin.le_def.mpr (by simp; omega)) w
      rw [← Fin.succ_castSucc] at hδ
      rw [← hδ, hup j.succ hj (by simp; omega)]
      convert (hy _ _ hbi hj (Fin.lt_def.mpr (by simp; omega))).symm using 3 <;>
        simp [Fin.ext_iff]
    · obtain rfl : j = b.succ := Fin.ext (by simpa using hbj.symm)
      rw [δ_mul hX, δ_comp_σ_succ_apply, mul_inv_cancel_left]

/-- Correcting the faces below `i` from the bottom up: for `r ≤ i` there is an `(m + 2)`-simplex
whose faces `j < r` are the `y j`. -/
private lemma exists_δ_eq_of_lt (r : ℕ) (hr : r ≤ i.val) :
    ∃ w : X _⦋m + 2⦌, ∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < r → X.δ j w = y j hj := by
  induction r with
  | zero => exact ⟨1, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ r ih =>
    obtain ⟨w, hw⟩ := ih (by omega)
    obtain ⟨w', hw'⟩ := exists_lower_step hX hy ⟨r, by omega⟩
      (Fin.ne_of_val_ne (by simp; omega)) w hw
    exact ⟨w', fun j hj hjr => hw' j hj (by simp; omega)⟩

/-- Correcting the faces above `i` from the top down, keeping those below `i`: for
`t ≤ m + 2 - i` there is an `(m + 2)`-simplex whose faces `j < i` and `j > m + 2 - t` are the
`y j`. -/
private lemma exists_δ_eq_of_lt_or_gt (t : ℕ) (ht : t ≤ m + 2 - i.val) :
    ∃ w : X _⦋m + 2⦌,
      (∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < i.val → X.δ j w = y j hj) ∧
      ∀ (j : Fin (m + 3)) (hj : j ≠ i), m + 2 - t < j.val → X.δ j w = y j hj := by
  induction t with
  | zero =>
    obtain ⟨w, hw⟩ := exists_δ_eq_of_lt hX hy i.val le_rfl
    exact ⟨w, hw, fun j _ hj => absurd hj (by omega)⟩
  | succ t ih =>
    obtain ⟨w, hw, hw'⟩ := ih (by omega)
    obtain ⟨w', hw₁, hw₂⟩ := exists_upper_step hX hy ⟨m + 1 - t, by omega⟩
      (Fin.ne_of_val_ne (by simp; omega)) (by simp; omega) w hw
      (fun j hj hjt => hw' j hj (by simp at hjt; omega))
    exact ⟨w', hw₁, fun j hj hjt => hw₂ j hj (by simp; omega)⟩

/-- **Horn filling in a simplicial group**: a compatible family of `m + 1`-simplices on the faces
`j ≠ i` of an `(m + 2)`-simplex is the family of faces of an `(m + 2)`-simplex. -/
private lemma exists_δ_eq_of_group : ∃ w : X _⦋m + 2⦌, ∀ (j : Fin (m + 3)) (hj : j ≠ i),
    X.δ j w = y j hj := by
  obtain ⟨w, hw, hw'⟩ := exists_δ_eq_of_lt_or_gt hX hy (m + 2 - i.val) le_rfl
  refine ⟨w, fun j hj => ?_⟩
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with h | h
  · exact hw j hj h
  · exact hw' j hj (by omega)

omit hy in
/-- **Moore's theorem**: a simplicial set whose sets of simplices are groups, with simplicial
operators group homomorphisms, is a Kan complex. -/
theorem kanComplex_of_group : X.KanComplex := by
  rw [KanComplex.iff]
  intro n i f hf
  suffices h : ∃ x : X _⦋n + 1⦌, ∀ (j : Fin (n + 2)) (hj : j ≠ i), X.δ j x = yonedaEquiv (f j hj) by
    obtain ⟨x, hx⟩ := h
    refine ⟨yonedaEquiv.symm x, fun j hj => ?_⟩
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, hx, Equiv.symm_apply_apply]
  cases n with
  | zero =>
    -- A one-dimensional horn is a single vertex, filled by its degenerate edge.
    obtain rfl | rfl := Fin.exists_fin_two.mp ⟨i, rfl⟩
    · refine ⟨X.σ 0 (yonedaEquiv (f 1 (by decide))), fun j hj => ?_⟩
      obtain rfl | rfl := Fin.exists_fin_two.mp ⟨j, rfl⟩
      · exact absurd rfl hj
      · exact δ_comp_σ_succ_apply 0 _
    · refine ⟨X.σ 0 (yonedaEquiv (f 0 (by decide))), fun j hj => ?_⟩
      obtain rfl | rfl := Fin.exists_fin_two.mp ⟨j, rfl⟩
      · exact δ_comp_σ_self_apply 0 _
      · exact absurd rfl hj
  | succ m =>
    refine exists_δ_eq_of_group hX (fun j k hj hk hjk => ?_)
    have := congrArg yonedaEquiv (hf.δ_pred_comp j k hj hk hjk)
    rwa [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at this

end Group

/-- **Moore's theorem** for additive groups: a simplicial set whose sets of simplices are additive
groups, with simplicial operators additive, is a Kan complex. -/
theorem kanComplex_of_addGroup {X : SSet.{u}} [∀ n, AddGroup (X.obj n)]
    (hX : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x y : X.obj m),
      X.map f (x + y) = X.map f x + X.map f y) :
    X.KanComplex :=
  letI : ∀ n, Group (X.obj n) := fun n => (inferInstance : Group (Multiplicative (X.obj n)))
  kanComplex_of_group fun _ _ f x y => hX f x y

end SSet

namespace CategoryTheory.SimplicialObject

/-- The underlying simplicial set of a simplicial group is a Kan complex. -/
instance kanComplex_comp_forget_grpCat (G : SimplicialObject GrpCat.{u}) :
    SSet.KanComplex (G ⋙ forget GrpCat) :=
  letI (n : SimplexCategoryᵒᵖ) : Group ((G ⋙ forget GrpCat).obj n) :=
    inferInstanceAs (Group (G.obj n))
  SSet.kanComplex_of_group (X := G ⋙ forget GrpCat) fun _ _ f x y => map_mul (G.map f).hom x y

/-- The underlying simplicial set of a simplicial abelian group is a Kan complex. -/
instance kanComplex_comp_forget_addCommGrpCat (G : SimplicialObject AddCommGrpCat.{u}) :
    SSet.KanComplex (G ⋙ forget AddCommGrpCat) :=
  letI (n : SimplexCategoryᵒᵖ) : AddGroup ((G ⋙ forget AddCommGrpCat).obj n) :=
    inferInstanceAs (AddGroup (G.obj n))
  SSet.kanComplex_of_addGroup (X := G ⋙ forget AddCommGrpCat) fun _ _ f x y =>
    map_add (G.map f).hom x y

/-- The underlying simplicial set of a simplicial module is a Kan complex. -/
instance kanComplex_comp_forget_moduleCat {R : Type*} [Ring R]
    (G : SimplicialObject (ModuleCat.{u} R)) : SSet.KanComplex (G ⋙ forget (ModuleCat R)) :=
  letI (n : SimplexCategoryᵒᵖ) : AddGroup ((G ⋙ forget (ModuleCat R)).obj n) :=
    inferInstanceAs (AddGroup (G.obj n))
  SSet.kanComplex_of_addGroup (X := G ⋙ forget (ModuleCat R)) fun _ _ f x y =>
    map_add (G.map f).hom x y

end CategoryTheory.SimplicialObject
