/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseUnconditional

/-!
# The `Δ[n] ⊗ Δ[2]` shuffle filtration (the supporting results)

This module is intended to formalize the additional comparison obligation of `CobaseUnconditional.lean`:
the shuffle filtration of the prism `Δ[n] ⊗ Δ[2]` and the two horn
extension properties over a cell,

```text
SSet.exists_extension_of_unionProd_boundary_horn_zero  -- from ∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,0]
SSet.exists_extension_of_unionProd_boundary_horn_two   -- from ∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,2]
```
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-!
## Arithmetic of the shuffle chains

The second coordinate of the shuffle `τ_{a,b}` at position `t`
is the threshold function `shuffleSnd a b t`; the first is
`shuffleFst a b t = t - shuffleSnd a b t`. All face computations
below reduce to the `ℕ`-level characterizations in this section.
-/

section ShuffleArithmetic

variable {a b t v : ℕ}

/-- Second coordinates of the shuffle `τ_{a,b}`: `0` up to
position `a`, `1` up to position `b + 1`, then `2`. -/
def shuffleSnd (a b t : ℕ) : ℕ :=
  if t ≤ a then 0 else if t ≤ b + 1 then 1 else 2

/-- First coordinates of the shuffle `τ_{a,b}`: `t` minus the
number of height jumps before position `t`. -/
def shuffleFst (a b t : ℕ) : ℕ :=
  t - shuffleSnd a b t

lemma shuffleSnd_le_two (a b t : ℕ) : shuffleSnd a b t ≤ 2 := by
  unfold shuffleSnd
  split_ifs <;> omega

lemma shuffleSnd_eq_zero : shuffleSnd a b t = 0 ↔ t ≤ a := by
  by_cases h1 : t ≤ a
  · simp [shuffleSnd, h1]
  · by_cases h2 : t ≤ b + 1 <;> simp [shuffleSnd, h1, h2]

lemma shuffleSnd_eq_one :
    shuffleSnd a b t = 1 ↔ a < t ∧ t ≤ b + 1 := by
  by_cases h1 : t ≤ a
  · simp [shuffleSnd, h1]
  · by_cases h2 : t ≤ b + 1 <;> simp [shuffleSnd, h1, h2]; omega

lemma shuffleSnd_eq_two (hab : a ≤ b) :
    shuffleSnd a b t = 2 ↔ b + 2 ≤ t := by
  by_cases h1 : t ≤ a
  · simp [shuffleSnd, h1]
    omega
  · by_cases h2 : t ≤ b + 1 <;> simp [shuffleSnd, h1, h2] <;> omega

lemma shuffleFst_add_snd (a b t : ℕ) :
    shuffleFst a b t + shuffleSnd a b t = t := by
  unfold shuffleFst shuffleSnd
  split_ifs <;> omega

/-- Occurrences of the first-coordinate value `v` in the shuffle
`τ_{a,b}`: at position `v` (when `v ≤ a`), `v + 1` (when
`a ≤ v ≤ b`) and `v + 2` (when `b ≤ v`); the double occurrences
are exactly the corners `(a,0),(a,1)` and `(b,1),(b,2)`. -/
lemma shuffleFst_eq_iff (hab : a ≤ b) :
    shuffleFst a b t = v ↔
      (t = v ∧ v ≤ a) ∨ (t = v + 1 ∧ a ≤ v ∧ v ≤ b) ∨
        (t = v + 2 ∧ b ≤ v) := by
  have hsum := shuffleFst_add_snd a b t
  have hcases : shuffleSnd a b t = 0 ∨ shuffleSnd a b t = 1 ∨
      shuffleSnd a b t = 2 := by
    have h2 := shuffleSnd_le_two a b t
    omega
  constructor
  · intro h
    rcases hcases with h0 | h1 | h2
    · have hle := shuffleSnd_eq_zero.1 h0
      exact Or.inl ⟨by omega, by omega⟩
    · obtain ⟨hgt, hle⟩ := shuffleSnd_eq_one.1 h1
      exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
    · have hge := (shuffleSnd_eq_two hab).1 h2
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · rintro (⟨htv, hv⟩ | ⟨htv, hv1, hv2⟩ | ⟨htv, hv⟩)
    · have h0 : shuffleSnd a b t = 0 :=
        shuffleSnd_eq_zero.2 (by omega)
      omega
    · have h1 : shuffleSnd a b t = 1 :=
        shuffleSnd_eq_one.2 ⟨by omega, by omega⟩
      omega
    · have h2 : shuffleSnd a b t = 2 :=
        (shuffleSnd_eq_two hab).2 (by omega)
      omega

lemma shuffleFst_le_of_le (hab : a ≤ b) (hb : b ≤ v) (ht : t ≤ v + 2) :
    shuffleFst a b t ≤ v := by
  have hsum := shuffleFst_add_snd a b t
  have hcases : shuffleSnd a b t = 0 ∨ shuffleSnd a b t = 1 ∨
      shuffleSnd a b t = 2 := by
    have h2 := shuffleSnd_le_two a b t
    omega
  rcases hcases with h0 | h1 | h2
  · have hle := shuffleSnd_eq_zero.1 h0
    omega
  · obtain ⟨-, hle⟩ := shuffleSnd_eq_one.1 h1
    omega
  · omega

/-- Shifting the first threshold up changes the height function
only at position `a + 1` (the corner where `τ_{a,b}` and
`τ_{a+1,b}` differ). -/
lemma shuffleSnd_succ_left (h : t ≠ a + 1) :
    shuffleSnd (a + 1) b t = shuffleSnd a b t := by
  unfold shuffleSnd
  split_ifs <;> omega

/-- Shifting the second threshold up changes the height
function only at position `b + 2`. -/
lemma shuffleSnd_succ_right (h : t ≠ b + 2) :
    shuffleSnd a (b + 1) t = shuffleSnd a b t := by
  unfold shuffleSnd
  split_ifs <;> omega

/-- Shifting the first threshold down changes the height
function only at position `a` (for `a ≥ 1`). -/
lemma shuffleSnd_pred_left (ha : 1 ≤ a) (h : t ≠ a) :
    shuffleSnd (a - 1) b t = shuffleSnd a b t := by
  unfold shuffleSnd
  split_ifs <;> omega

/-- Shifting the second threshold down changes the height
function only at position `b + 1` (for `b ≥ 1`). -/
lemma shuffleSnd_pred_right (hb : 1 ≤ b) (h : t ≠ b + 1) :
    shuffleSnd a (b - 1) t = shuffleSnd a b t := by
  unfold shuffleSnd
  split_ifs <;> omega

end ShuffleArithmetic

/-!
## The top simplices `τ_{a,b}` of `Δ[n] ⊗ Δ[2]`

The shuffle `τ_{a,b}` is the chain `(0,0), …, (a,0), (a,1), …,
(b,1), (b,2), …, (n,2)` read through
`SSet.prodStdSimplex.objEquiv`. We record its values, range,
nondegeneracy, the classification of nondegenerate top
simplices, injectivity of its classifying map, and the face
analysis: non-corner faces lie over `∂Δ[n]`, and the two
"moving" corner faces agree with the corresponding faces of the
adjacent shuffles.
-/

section ShuffleTau

variable {n a b : ℕ}

/-- The `(a,b)`-shuffle: the nondegenerate `(n+2)`-simplex of
`Δ[n] ⊗ Δ[2]` with vertices `(0,0), …, (a,0), (a,1), …, (b,1),
(b,2), …, (n,2)`. -/
noncomputable def shuffleTau (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋n + 2⦌ :=
  prodStdSimplex.objEquiv.symm
    ⟨fun t ↦ (⟨shuffleFst a b t.val, by
        have ht : t.val ≤ n + 2 := by have h2 := t.2; omega
        have hle := shuffleFst_le_of_le hab hb ht
        omega⟩,
      ⟨shuffleSnd a b t.val, by
        have hle := shuffleSnd_le_two a b t.val
        omega⟩), by
      intro s t hst
      have hval : s.val ≤ t.val := hst
      refine ⟨?_, ?_⟩
      · change shuffleFst a b s.val ≤ shuffleFst a b t.val
        unfold shuffleFst shuffleSnd
        split_ifs <;> omega
      · change shuffleSnd a b s.val ≤ shuffleSnd a b t.val
        unfold shuffleSnd
        split_ifs <;> omega⟩

/-- The map `Δ[n+2] ⟶ Δ[n] ⊗ Δ[2]` classifying `shuffleTau`. -/
noncomputable abbrev shuffleTauMap (n a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ n) :
    Δ[n + 2] ⟶ (Δ[n] ⊗ Δ[2] : SSet.{u}) :=
  yonedaEquiv.symm (shuffleTau n a b hab hb)

lemma shuffleTau_objEquiv_fst_val (hab : a ≤ b) (hb : b ≤ n)
    (t : Fin (n + 3)) :
    ((prodStdSimplex.objEquiv (shuffleTau n a b hab hb) t).1).val =
      shuffleFst a b t.val :=
  rfl

lemma shuffleTau_objEquiv_snd_val (hab : a ≤ b) (hb : b ≤ n)
    (t : Fin (n + 3)) :
    ((prodStdSimplex.objEquiv (shuffleTau n a b hab hb) t).2).val =
      shuffleSnd a b t.val :=
  rfl

lemma shuffleTau_objEquiv_apply_eq_iff (hab : a ≤ b) (hb : b ≤ n)
    (t : Fin (n + 3)) {p : Fin (n + 1) × Fin 3} :
    prodStdSimplex.objEquiv (shuffleTau n a b hab hb) t = p ↔
      shuffleFst a b t.val = p.1.val ∧
        shuffleSnd a b t.val = p.2.val := by
  constructor
  · intro h
    constructor
    · have h1 := congrArg Fin.val (congrArg Prod.fst h)
      rwa [shuffleTau_objEquiv_fst_val hab hb t] at h1
    · have h2 := congrArg Fin.val (congrArg Prod.snd h)
      rwa [shuffleTau_objEquiv_snd_val hab hb t] at h2
  · rintro ⟨h1, h2⟩
    apply Prod.ext <;> apply Fin.ext
    · rw [shuffleTau_objEquiv_fst_val hab hb t, h1]
    · rw [shuffleTau_objEquiv_snd_val hab hb t, h2]

/-- The range of `τ_{a,b}` is
`{(i,0) | i ≤ a} ∪ {(i,1) | a ≤ i ≤ b} ∪ {(i,2) | b ≤ i}`. -/
lemma mem_range_shuffleTau_objEquiv (hab : a ≤ b) (hb : b ≤ n)
    {p : Fin (n + 1) × Fin 3} :
    p ∈ Set.range
        (prodStdSimplex.objEquiv (shuffleTau n a b hab hb)) ↔
      (p.2.val = 0 ∧ p.1.val ≤ a) ∨
        (p.2.val = 1 ∧ a ≤ p.1.val ∧ p.1.val ≤ b) ∨
          (p.2.val = 2 ∧ b ≤ p.1.val) := by
  constructor
  · rintro ⟨t, ht⟩
    rw [shuffleTau_objEquiv_apply_eq_iff hab hb t] at ht
    obtain ⟨hf, hs⟩ := ht
    have hsum := shuffleFst_add_snd a b t.val
    have hpc : p.2.val = 0 ∨ p.2.val = 1 ∨ p.2.val = 2 := by
      have h3 := p.2.2
      omega
    rcases hpc with h0 | h1 | h2
    · have hle : t.val ≤ a :=
        (shuffleSnd_eq_zero (a := a) (b := b) (t := t.val)).1 (by omega)
      exact Or.inl ⟨h0, by omega⟩
    · obtain ⟨hgt, hle⟩ := shuffleSnd_eq_one.1 (by omega :
        shuffleSnd a b t.val = 1)
      exact Or.inr (Or.inl ⟨h1, by omega, by omega⟩)
    · have hge : b + 2 ≤ t.val := (shuffleSnd_eq_two hab).1 (by omega)
      exact Or.inr (Or.inr ⟨h2, by omega⟩)
  · rintro (⟨h2, h1⟩ | ⟨h2, h1, h1'⟩ | ⟨h2, h1⟩)
    · refine ⟨⟨p.1.val + p.2.val, by
          have e1 := p.1.2
          have e2 := p.2.2
          omega⟩, ?_⟩
      rw [shuffleTau_objEquiv_apply_eq_iff hab hb _]
      exact ⟨(shuffleFst_eq_iff hab).2 (Or.inl
          ⟨by change p.1.val + p.2.val = p.1.val; omega, h1⟩),
        by change shuffleSnd a b (p.1.val + p.2.val) = p.2.val
           have h := (shuffleSnd_eq_zero (a := a) (b := b)
             (t := p.1.val + p.2.val)).2 (by omega)
           omega⟩
    · refine ⟨⟨p.1.val + p.2.val, by
          have e1 := p.1.2
          have e2 := p.2.2
          omega⟩, ?_⟩
      rw [shuffleTau_objEquiv_apply_eq_iff hab hb _]
      exact ⟨(shuffleFst_eq_iff hab).2
          (Or.inr (Or.inl
            ⟨by change p.1.val + p.2.val = p.1.val + 1; omega, h1, h1'⟩)),
        by change shuffleSnd a b (p.1.val + p.2.val) = p.2.val
           have h := (shuffleSnd_eq_one (a := a) (b := b)
             (t := p.1.val + p.2.val)).2 ⟨by omega, by omega⟩
           omega⟩
    · refine ⟨⟨p.1.val + p.2.val, by
          have e1 := p.1.2
          have e2 := p.2.2
          omega⟩, ?_⟩
      rw [shuffleTau_objEquiv_apply_eq_iff hab hb _]
      exact ⟨(shuffleFst_eq_iff hab).2 (Or.inr (Or.inr
          ⟨by change p.1.val + p.2.val = p.1.val + 2; omega, h1⟩)),
        by change shuffleSnd a b (p.1.val + p.2.val) = p.2.val
           have h := (shuffleSnd_eq_two (a := a) (b := b)
             (t := p.1.val + p.2.val) hab).2 (by omega)
           omega⟩

end ShuffleTau

end SSet

end
