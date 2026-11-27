/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOne

/-!
# A nondependent index for the gap-one Shih family

Gap-one Shih indices are equivalently a front degree `p+1 > 0` together with
a shuffle whose complementary degree is forced by the ambient degree.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicTopology.EilenbergZilber.ShihIndex

/-- Gap-one data with the forced second shuffle degree made explicit. -/
def GapOneShuffleIndex (n : ℕ) :=
  Σ p : Fin n, Shuffle ((p : ℕ) + 1) (n - ((p : ℕ) + 1))

noncomputable instance (n : ℕ) : Fintype (GapOneShuffleIndex n) := by
  unfold GapOneShuffleIndex
  infer_instance

def toGapOneShuffleIndex {n : ℕ}
    (i : {i : ShihIndex n // i.gap = 1}) : GapOneShuffleIndex n :=
  ⟨i.1.p, Eq.ndrec i.1.shuffle (by
    have h := i.1.q_eq_of_gap_eq_one i.2
    omega)⟩

def ofGapOneShuffleIndex {n : ℕ} (x : GapOneShuffleIndex n) :
    {i : ShihIndex n // i.gap = 1} := by
  let q : Fin (n - (x.1 : ℕ)) :=
    ⟨n - ((x.1 : ℕ) + 1), by
      have hp := x.1.isLt
      omega⟩
  let s : Shuffle ((x.1 : ℕ) + 1) q := Eq.ndrec x.2 (by rfl)
  refine ⟨⟨x.1, q, s⟩, ?_⟩
  rw [gap]
  dsimp [q]
  have hp := x.1.isLt
  omega

/-- Classification of gap-one Shih indices by a front degree `p+1` and its
shuffle. -/
def gapOneEquiv (n : ℕ) :
    {i : ShihIndex n // i.gap = 1} ≃ GapOneShuffleIndex n where
  toFun := toGapOneShuffleIndex
  invFun := ofGapOneShuffleIndex
  left_inv i := by
    apply Subtype.ext
    rcases i with ⟨⟨p, q, s⟩, hi⟩
    dsimp only [toGapOneShuffleIndex, ofGapOneShuffleIndex]
    congr 1
    · apply Fin.ext
      have h := q_eq_of_gap_eq_one ⟨p, q, s⟩ hi
      change (q : ℕ) = n - 1 - (p : ℕ) at h
      simp only
      omega
    · exact eqRec_heq _ s
  right_inv x := by
    rcases x with ⟨p, s⟩
    dsimp only [toGapOneShuffleIndex, ofGapOneShuffleIndex]

theorem sum_gap_one {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : ShihIndex n → A) :
  ∑ i : {i : ShihIndex n // i.gap = 1}, f i.1 =
      ∑ x : GapOneShuffleIndex n, f ((gapOneEquiv n).symm x).1 := by
  exact Fintype.sum_equiv (gapOneEquiv n) _ _ fun i => by simp

end AlgebraicTopology.EilenbergZilber.ShihIndex
