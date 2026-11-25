/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ContinuousOn


/-!
# Tree-like paths

Hambly and Lyons call a path `X : [0, T] → V` *tree-like* if some continuous height function
`h ≥ 0` vanishing at both ends controls its increments by
`‖X_t − X_s‖ ≤ h(s) + h(t) − 2 inf_{u ∈ [s,t]} h(u)` (B. Hambly and T. Lyons, *Uniqueness for the
signature of a path of bounded variation and the reduced path group*, Ann. of Math. 171 (2010),
Definition 1.3). Tree-like paths are exactly the paths of bounded variation with trivial signature
(their Theorem 1); that theorem is recorded as
`MathlibExt.Analysis.PathSignature.TreeLikeWanted.isTreeLike_iff_signature_eq_tensorOne`.

Here we give the definition and two examples: constant paths, and a segment traversed out and
back.
-/

@[expose] public section

namespace MathlibExt.Analysis.PathSignature

/-- **Tree-like path (Hambly–Lyons).** A path `X : [0, T] → E` in a normed group is tree-like if
there is a continuous function `h : [0, T] → [0, ∞)` with `h 0 = h T = 0` such that
`‖X_t − X_s‖ ≤ h(s) + h(t) − 2 inf_{u ∈ [s,t]} h(u)` for all `0 ≤ s ≤ t ≤ T`; `h` is a height
function for `X` (B. Hambly and T. Lyons, *Uniqueness for the signature of a path of bounded
variation and the reduced path group*, Ann. of Math. 171 (2010), arXiv:math/0507536,
Definition 1.3). The definition is meant for `T ≥ 0`: for `T < 0` the interval is empty and
every path qualifies. -/
def IsTreeLike {E : Type*} [NormedAddCommGroup E] (X : ℝ → E) (T : ℝ) : Prop :=
  ∃ h : ℝ → ℝ, ContinuousOn h (Set.Icc 0 T) ∧ (∀ t ∈ Set.Icc 0 T, 0 ≤ h t) ∧ h 0 = 0 ∧
    h T = 0 ∧ ∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc s T,
      ‖X t - X s‖ ≤ h s + h t - 2 * sInf (h '' Set.Icc s t)

/-- **Constant paths are tree-like**, with height function `0`. -/
theorem isTreeLike_const {E : Type*} [NormedAddCommGroup E] (x : E) (T : ℝ) :
    IsTreeLike (fun _ => x) T := by
  refine ⟨fun _ => 0, continuousOn_const, fun _ _ => le_rfl, rfl, rfl, fun s _ t ht => ?_⟩
  have hne : (Set.Icc s t).Nonempty := ⟨s, le_rfl, ht.1⟩
  simp [hne.image_const]

/-- **A segment traversed out and back is tree-like.** For `x` in a normed space and `T ≥ 0`, the
path `t ↦ min t (T − t) • x` runs linearly from `0` to `(T/2) x` and back to `0`; the height
function `h(t) = min(t, T − t) ‖x‖` witnesses that it is tree-like in the sense of Hambly and
Lyons (Ann. of Math. 171 (2010), Definition 1.3). -/
theorem isTreeLike_out_and_back {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    {T : ℝ} (hT : 0 ≤ T) : IsTreeLike (fun t => min t (T - t) • x) T := by
  set φ : ℝ → ℝ := fun t => min t (T - t)
  have hφc : Continuous φ := continuous_id.min (continuous_const.sub continuous_id)
  refine ⟨fun t => φ t * ‖x‖, (hφc.mul continuous_const).continuousOn,
    fun t ht => mul_nonneg (le_min ht.1 (sub_nonneg.mpr ht.2)) (norm_nonneg x),
    by simp [φ, hT], by simp [φ, hT], fun s hs t ht => ?_⟩
  have hst : s ≤ t := ht.1
  have hne : (Set.Icc s t).Nonempty := ⟨s, le_rfl, hst⟩
  have hbdd : BddBelow ((fun u => φ u * ‖x‖) '' Set.Icc s t) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact mul_nonneg (le_min (hs.1.trans hu.1) (sub_nonneg.mpr (hu.2.trans ht.2)))
      (norm_nonneg x)
  have hinf_s : sInf ((fun u => φ u * ‖x‖) '' Set.Icc s t) ≤ φ s * ‖x‖ :=
    csInf_le hbdd ⟨s, ⟨le_rfl, hst⟩, rfl⟩
  have hinf_t : sInf ((fun u => φ u * ‖x‖) '' Set.Icc s t) ≤ φ t * ‖x‖ :=
    csInf_le hbdd ⟨t, ⟨hst, le_rfl⟩, rfl⟩
  have hnorm : ‖φ t • x - φ s • x‖ = |φ t - φ s| * ‖x‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  change ‖φ t • x - φ s • x‖ ≤ _
  rw [hnorm]
  rcases le_total (φ s) (φ t) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith [norm_nonneg x]
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith [norm_nonneg x]

/-- **A tree-like path is a loop.** If `X` is tree-like on `[0, T]` with `T ≥ 0`, then
`X_T = X_0`: the pair of times `(0, T)` gives `‖X_T − X_0‖ ≤ −2 inf h ≤ 0` (B. Hambly and T. Lyons,
Ann. of Math. 171 (2010), Definition 1.3). In particular a segment with distinct endpoints is not
tree-like. -/
theorem IsTreeLike.apply_eq {E : Type*} [NormedAddCommGroup E] {X : ℝ → E} {T : ℝ}
    (hX : IsTreeLike X T) (hT : 0 ≤ T) : X T = X 0 := by
  obtain ⟨h, -, hnn, h0, hT0, hineq⟩ := hX
  have hinf : 0 ≤ sInf (h '' Set.Icc 0 T) :=
    Real.sInf_nonneg fun _ ⟨u, hu, hux⟩ => hux ▸ hnn u hu
  have := hineq 0 ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩
  rw [h0, hT0] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (by linarith))

end MathlibExt.Analysis.PathSignature
