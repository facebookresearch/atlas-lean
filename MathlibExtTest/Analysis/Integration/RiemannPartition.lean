/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Integration.RiemannCommonRefinement
import Mathlib.Tactic

namespace MetaMathlibExt

open MathlibExt.Analysis.Integration

/-- The endpoints of any partition satisfy `a ≤ b`. -/
example {a b : ℝ} (P : Partition a b) : a ≤ b :=
  P.a_le_b

/-- A partition of `[a, b]` with `a < b` has positive mesh. -/
example {a b : ℝ} (hab : a < b) (P : Partition a b) : 0 < P.mesh :=
  P.mesh_pos_of_lt hab

/-- The subinterval lengths of any partition telescope to `b - a`. -/
example {a b : ℝ} (P : Partition a b) :
    ∑ i : Fin P.n, (P.points i.succ - P.points i.castSucc) = b - a :=
  P.sum_sub_eq

/-- Every tag of a tagged partition lies in `[a, b]`. -/
example {a b : ℝ} (T : TaggedPartition a b) (i : Fin T.n) :
    T.tags i ∈ Set.Icc a b :=
  T.tag_mem_Icc i

/-- The Riemann sum of a constant function is the constant times `b - a`. -/
example {a b : ℝ} (c : ℝ) (T : TaggedPartition a b) :
    riemannSum (fun _ => c) T = c * (b - a) :=
  riemannSum_const c T

/-- The Riemann sum over a trivial tagged partition is `0`. -/
example {a b : ℝ} (f : ℝ → ℝ) (T : TaggedPartition a b) (h : T.n = 0) :
    riemannSum f T = 0 :=
  riemannSum_eq_zero_of_n_eq_zero f T h

/-- Every tagged partition is a tagged refinement of itself, with `assign`
the identity. -/
example {a b : ℝ} (T : TaggedPartition a b) : T.IsTaggedRefinement T where
  assign := id
  contained_left := fun _ => le_rfl
  contained_right := fun _ => le_rfl
  telescope := fun k => by
    -- Only `k` itself survives the filter `id j = k`.
    have : Finset.univ.filter (fun j : Fin T.n => id j = k) = {k} := by
      ext j
      simp [Finset.mem_filter, Finset.mem_singleton]
    rw [this]
    simp

/-- For a constant function, the refinement bound holds with oscillation
`0`: the two Riemann sums are equal. -/
example {a b : ℝ} (c : ℝ) (T T' : TaggedPartition a b)
    (href : T.IsTaggedRefinement T') :
    |riemannSum (fun _ => c) T - riemannSum (fun _ => c) T'| ≤ (0 : ℝ) * (b - a) := by
  apply riemannSum_sub_le_of_isTaggedRefinement _ T T' _ href
  intro x _ y _ _
  simp

/-- Any two tagged partitions have a common tagged refinement. -/
example {a b : ℝ} (T₁ T₂ : TaggedPartition a b) :
    ∃ T'' : TaggedPartition a b,
      Nonempty (T₁.IsTaggedRefinement T'') ∧
        Nonempty (T₂.IsTaggedRefinement T'') :=
  TaggedPartition.exists_commonRefinement T₁ T₂

/-- For a constant function, the common-refinement bound holds with
oscillations `0`: the two Riemann sums are equal. -/
example {a b : ℝ} (c : ℝ) (T₁ T₂ : TaggedPartition a b) :
    |riemannSum (fun _ => c) T₁ - riemannSum (fun _ => c) T₂| ≤
      ((0 : ℝ) + 0) * (b - a) := by
  obtain ⟨T'', ⟨href₁⟩, ⟨href₂⟩⟩ := TaggedPartition.exists_commonRefinement T₁ T₂
  apply riemannSum_sub_le_of_commonRefinement _ T₁ T₂ _ _ T'' href₁ href₂ <;>
    intro x _ y _ _ <;> simp

/-- The one-subinterval tagged partition of `[0, 1]` with tag `1 / 2`:
the Riemann sum of the identity function is `1 / 2`. -/
example : ∃ T : TaggedPartition (0 : ℝ) 1,
    T.n = 1 ∧ riemannSum (fun x => x) T = 1 / 2 := by
  refine ⟨{
    n := 1
    points := fun i => (i : ℝ)
    ordered := by
      intro a b hab
      dsimp only
      exact_mod_cast hab
    first := by simp
    last := by simp
    tags := fun _ => 1 / 2
    tag_mem := by
      intro i
      fin_cases i; simp; norm_num
  }, rfl, ?_⟩
  simp [riemannSum]

end MetaMathlibExt
