/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle

/-!
# Indices for the Eilenberg--Mac Lane homotopy

This file packages the finite indexing set and sign in the explicit Shih
formula. An index in Lean degree `n` consists of natural numbers `p`, `q`
with `p + q < n`, together with a `(p + 1, q)`-shuffle. In the source
notation described in `ShihFormula`, its degree `m` is this `n`, while
`\bar m = m - p - q` is `gap`.
-/

@[expose] public section

set_option autoImplicit false

namespace AlgebraicTopology.EilenbergZilber

/-- The finite indexing type for the explicit Shih homotopy in degree `n`.

The dependent bounds encode `p + q < n` without retaining a separate proof
field. -/
structure ShihIndex (n : ℕ) where
  p : Fin n
  q : Fin (n - p)
  shuffle : Shuffle (p + 1) q

namespace ShihIndex

noncomputable instance (n : ℕ) : Fintype (ShihIndex n) :=
  let e : ShihIndex n ≃ Σ p : Fin n, Σ q : Fin (n - p), Shuffle (p + 1) q :=
    { toFun := fun i => ⟨i.p, i.q, i.shuffle⟩
      invFun := fun i => ⟨i.1, i.2.1, i.2.2⟩
      left_inv := fun i => by cases i; rfl
      right_inv := fun i => by rcases i with ⟨p, q, s⟩; rfl }
  Fintype.ofEquiv (Σ p : Fin n, Σ q : Fin (n - p), Shuffle (p + 1) q) e.symm

/-- The positive gap `n - p - q`, denoted `\bar m` in the source formula,
where the source's input degree `m` is Lean's `n`. -/
def gap {n : ℕ} (i : ShihIndex n) : ℕ := n - i.p - i.q

theorem add_lt {n : ℕ} (i : ShihIndex n) : (i.p : ℕ) + i.q < n := by
  have hp : (i.p : ℕ) < n := i.p.isLt
  have hq : (i.q : ℕ) < n - i.p := i.q.isLt
  omega

theorem gap_pos {n : ℕ} (i : ShihIndex n) : 0 < i.gap := by
  rw [gap]
  omega

theorem p_add_q_add_gap {n : ℕ} (i : ShihIndex n) :
    (i.p : ℕ) + i.q + i.gap = n := by
  rw [gap]
  omega

/-- The source coefficient `(-1)^(\bar m + sig(α, β) + 1)`. -/
def sign {n : ℕ} (i : ShihIndex n) : ℤ :=
  (-1) ^ (i.gap + 1) * shuffleSignZ i.shuffle

end ShihIndex

end AlgebraicTopology.EilenbergZilber
