/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihIndex

/-!
# Recursive decomposition of Shih indices

Increasing the ambient degree preserves `p`, `q`, and the shuffle while adding
one to the positive gap.  Thus the terms with gap greater than one are exactly
the shifted terms from the previous degree, and their coefficients acquire a
minus sign.  The complementary gap-one terms are the front boundary family in
the classical recursive proof.
-/

@[expose] public section

set_option autoImplicit false

namespace AlgebraicTopology.EilenbergZilber.ShihIndex

/-- Raise the ambient degree of a Shih index, preserving its shuffle. -/
def succ {n : ℕ} (i : ShihIndex n) : ShihIndex (n + 1) :=
  { p := ⟨i.p, by omega⟩
    q := ⟨i.q, by
      change (i.q : ℕ) < n + 1 - (i.p : ℕ)
      have hi : (i.q : ℕ) < n - (i.p : ℕ) := i.q.isLt
      omega⟩
    shuffle := i.shuffle }

@[simp]
theorem succ_p {n : ℕ} (i : ShihIndex n) : (i.succ.p : ℕ) = i.p := rfl

@[simp]
theorem succ_q {n : ℕ} (i : ShihIndex n) : (i.succ.q : ℕ) = i.q := rfl

@[simp]
theorem succ_shuffle {n : ℕ} (i : ShihIndex n) :
    i.succ.shuffle = i.shuffle := rfl

@[simp]
theorem succ_gap {n : ℕ} (i : ShihIndex n) : i.succ.gap = i.gap + 1 := by
  rw [gap, gap]
  change n + 1 - (i.p : ℕ) - (i.q : ℕ) =
    (n - (i.p : ℕ) - (i.q : ℕ)) + 1
  have hp := i.p.isLt
  have hq := i.q.isLt
  omega

theorem succ_gap_gt_one {n : ℕ} (i : ShihIndex n) : 1 < i.succ.gap := by
  rw [succ_gap]
  exact Nat.succ_lt_succ i.gap_pos

@[simp]
theorem succ_sign {n : ℕ} (i : ShihIndex n) : i.succ.sign = -i.sign := by
  simp only [sign, succ_gap]
  change (-1 : ℤ) ^ (i.gap + 1 + 1) * shuffleSignZ i.shuffle =
    -((-1 : ℤ) ^ (i.gap + 1) * shuffleSignZ i.shuffle)
  rw [show i.gap + 1 + 1 = (i.gap + 1) + 1 by omega, pow_succ]
  ring

/-- Lower a Shih index whose gap is greater than one. -/
def pred {n : ℕ} (i : ShihIndex (n + 1)) (hi : 1 < i.gap) : ShihIndex n :=
  { p := ⟨i.p, by
      have hp := i.p.isLt
      have hsum := i.p_add_q_add_gap
      omega⟩
    q := ⟨i.q, by
      change (i.q : ℕ) < n - (i.p : ℕ)
      have hsum := i.p_add_q_add_gap
      omega⟩
    shuffle := i.shuffle }

@[simp]
theorem pred_p {n : ℕ} (i : ShihIndex (n + 1)) (hi : 1 < i.gap) :
    ((i.pred hi).p : ℕ) = i.p := rfl

@[simp]
theorem pred_q {n : ℕ} (i : ShihIndex (n + 1)) (hi : 1 < i.gap) :
    ((i.pred hi).q : ℕ) = i.q := rfl

@[simp]
theorem pred_gap {n : ℕ} (i : ShihIndex (n + 1)) (hi : 1 < i.gap) :
    (i.pred hi).gap + 1 = i.gap := by
  rw [gap, gap]
  change (n - (i.p : ℕ) - (i.q : ℕ)) + 1 =
    n + 1 - (i.p : ℕ) - (i.q : ℕ)
  have hsum := i.p_add_q_add_gap
  omega

/-- Gap-greater-than-one indices in degree `n+1` are precisely degree-`n`
indices. -/
def succEquiv (n : ℕ) :
    ShihIndex n ≃ {i : ShihIndex (n + 1) // 1 < i.gap} where
  toFun i := ⟨i.succ, i.succ_gap_gt_one⟩
  invFun i := i.1.pred i.2
  left_inv i := by
    rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, s⟩
    rfl
  right_inv i := by
    rcases i with ⟨⟨⟨p, hp⟩, ⟨q, hq⟩, s⟩, hi⟩
    rfl

theorem sum_gap_gt_one {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : ShihIndex (n + 1) → A) :
    ∑ i : {i : ShihIndex (n + 1) // 1 < i.gap}, f i =
      ∑ i : ShihIndex n, f i.succ := by
  exact (Fintype.sum_equiv (succEquiv n) (fun i => f i.succ)
    (fun i => f i.1) fun _ => rfl).symm

end AlgebraicTopology.EilenbergZilber.ShihIndex
