/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# f-divergences on finite alphabets

For a function `f` and distributions `P, Q` on a finite alphabet with `Q > 0`, the f-divergence is
`D_f(P ‖ Q) = ∑ₐ Q(a) f(P(a) / Q(a))` (Csiszár–Shields, *Information Theory and Statistics: A
Tutorial*, 2004, Section 4). For `f` convex on `[0, ∞)`:

* `sum_mul_comp_div_le`: the analogue (4.1) of the log-sum inequality;
* `fDiv_map_le`: the lumping property, `D_f(P^B ‖ Q^B) ≤ D_f(P ‖ Q)` for the lumpings along any map
  (Lemma 4.1), the finite form of data processing under deterministic maps;
* `fDiv_nonneg`: `D_f(P ‖ Q) ≥ 0` when `f(1) = 0` (Lemma 4.1);
* `fDiv_mul_log`: with `f(t) = t log t`, `D_f(P ‖ Q) = ∑ₐ P(a) log (P(a) / Q(a))`, the I-divergence.

Restrictions with respect to the source: `Q` is strictly positive, so the conventions for
`Q(a) = 0` are not needed, and `f` is real-valued and convex on `[0, ∞)`, which excludes `f(t) =
-log t` (the reversed divergence) at `P(a) = 0`. The value `f 0` is used as given; it is the
source's `f(0) = lim_{t → 0⁺} f(t)` when `f` is continuous at `0` from the right.
-/

@[expose] public section

namespace MathlibExt.InformationTheory.FDivergence

open Finset Real

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- **f-divergence on a finite alphabet** (Csiszár–Shields, *Information Theory and Statistics: A
Tutorial*, 2004, Section 4, definition of `D_f(P ‖ Q)`). For `f : ℝ → ℝ` and `P, Q : α → ℝ`,
`fDiv f P Q = ∑ₐ Q(a) f(P(a) / Q(a))`. It is meant for `Q > 0`; where `Q(a) = 0` the term is `0`
(Lean's `0 * x = 0`), which is the source's convention only when `P(a) = 0`. The value `f 0` is
used as given, whereas the source sets `f(0) = lim_{t → 0⁺} f(t)`; the two agree when `f` is
continuous at `0` from the right. -/
noncomputable def fDiv (f : ℝ → ℝ) (P Q : α → ℝ) : ℝ :=
  ∑ a, Q a * f (P a / Q a)

/-- **Lumping of a distribution along a map** (Csiszár–Shields, *Information Theory and Statistics:
A Tutorial*, 2004, Section 4, the `B`-lumping `P^B(i) = ∑_{a ∈ B_i} P(a)`). For `g : α → β`,
`lump g P b = ∑_{a : g a = b} P(a)`; the partition is the family of fibres of `g`. -/
def lump (g : α → β) (P : α → ℝ) (b : β) : ℝ :=
  ∑ a ∈ univ.filter (fun a => g a = b), P a

/-- **Generalised log-sum inequality** (Csiszár–Shields, *Information Theory and Statistics: A
Tutorial*, 2004, inequality (4.1)). For `f` convex on `[0, ∞)`, a finite set `s`, `aᵢ ≥ 0` and
`bᵢ > 0`, `(∑ bᵢ) f((∑ aᵢ) / (∑ bᵢ)) ≤ ∑ bᵢ f(aᵢ / bᵢ)`. -/
theorem sum_mul_comp_div_le {ι : Type*} {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    (s : Finset ι) (hs : s.Nonempty) {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, b i) * f ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, b i * f (a i / b i) := by
  have hB : 0 < ∑ i ∈ s, b i := Finset.sum_pos hb hs
  have hJ := hf.map_sum_le (t := s) (w := fun i => b i / ∑ j ∈ s, b j) (p := fun i => a i / b i)
    (fun i hi => (div_pos (hb i hi) hB).le)
    (by rw [← Finset.sum_div, div_self hB.ne'])
    (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hb i hi).le))
  have h1 : ∑ i ∈ s, (b i / ∑ j ∈ s, b j) • (a i / b i) = (∑ i ∈ s, a i) / ∑ i ∈ s, b i := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [smul_eq_mul]; field_simp [(hb i hi).ne']
  have h2 : ∑ i ∈ s, (b i / ∑ j ∈ s, b j) • f (a i / b i) =
      (∑ i ∈ s, b i * f (a i / b i)) / ∑ i ∈ s, b i := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; ring
  rw [h1, h2, le_div_iff₀ hB] at hJ
  linarith

/-- **Lumping property of f-divergences** (Csiszár–Shields, *Information Theory and Statistics: A
Tutorial*, 2004, Lemma 4.1, lumping property). For `f` convex on `[0, ∞)`, `P ≥ 0`, `Q > 0` and
any map `g : α → β`, `D_f(P^g ‖ Q^g) ≤ D_f(P ‖ Q)`, where `P^g, Q^g` are the lumpings along the
fibres of `g`. Letters of `β` outside the range of `g` contribute `0` on the left, the source's
convention `0 f(0/0) = 0`. -/
theorem fDiv_map_le {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) {P Q : α → ℝ}
    (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 < Q a) (g : α → β) :
    fDiv f (lump g P) (lump g Q) ≤ fDiv f P Q := by
  unfold fDiv
  rw [← Finset.sum_fiberwise univ g (fun a => Q a * f (P a / Q a))]
  refine Finset.sum_le_sum fun b _ => ?_
  rcases (univ.filter fun a => g a = b).eq_empty_or_nonempty with he | hne
  · simp [lump, he]
  · exact sum_mul_comp_div_le hf _ hne (fun a _ => hP a) (fun a _ => hQ a)

/-- **Nonnegativity of f-divergences** (Csiszár–Shields, *Information Theory and Statistics: A
Tutorial*, 2004, Lemma 4.1, first assertion). For `f` convex on `[0, ∞)` with `f(1) = 0`, and
distributions `P ≥ 0`, `Q > 0` (both summing to `1`) on a nonempty finite alphabet,
`D_f(P ‖ Q) ≥ 0`. -/
theorem fDiv_nonneg [Nonempty α] {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) (hf1 : f 1 = 0)
    {P Q : α → ℝ} (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 < Q a) (hP1 : ∑ a, P a = 1)
    (hQ1 : ∑ a, Q a = 1) : 0 ≤ fDiv f P Q := by
  have h := sum_mul_comp_div_le hf univ univ_nonempty (fun a _ => hP a) (fun a _ => hQ a)
  rw [hP1, hQ1, div_one, hf1, mul_zero] at h
  exact h

omit [Fintype β] [DecidableEq β] in
/-- **The I-divergence is the f-divergence of `t log t`** (Csiszár–Shields, *Information Theory
and Statistics: A Tutorial*, 2004, Section 4, example (1)). For `Q > 0`,
`D_f(P ‖ Q) = ∑ₐ P(a) log (P(a) / Q(a))` with `f(t) = t log t`. -/
theorem fDiv_mul_log {P Q : α → ℝ} (hQ : ∀ a, 0 < Q a) :
    fDiv (fun t => t * log t) P Q = ∑ a, P a * log (P a / Q a) := by
  unfold fDiv
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp [(hQ a).ne']

end MathlibExt.InformationTheory.FDivergence
