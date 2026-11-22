/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/RisingSun.lean` (leanprover/lean-eval, https://github.com/leanprover/lean-eval),
problem `rising_sun_lemma`, at commit 38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/rising_sun_lemma.toml`, rev 1, submitter Kim Morrison, status archived):
the definitions `risingSunSet`, `HasRisingSunDecomposition` and `HasRisingSunProperty` and the
statement of `rising_sun_lemma`, with the docstrings and comments they had in the former wanted
module `WantedExt/Analysis/RisingSunWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the `MathlibExt.Analysis.RisingSunWanted`
namespace. Mathematical statements are unchanged. Later change (ATLAS, 2026): the
`theorem_wanted` was proved and the declarations moved from
`WantedExt/Analysis/RisingSunWanted.lean` to this `MathlibExt` module with unchanged names,
statements and docstrings, and the imports of `Batteries.Util.ProofWanted` and of all of Mathlib
were replaced by a narrower Mathlib import.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`rising_sun_lemma`, the private lemmas it uses, the module documentation and the linter options.
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Riesz's rising sun lemma

For `f : ℝ → ℝ` and real numbers `a, b`, the rising sun set `risingSunSet a b f` is the set of
points `x ∈ (a, b)` such that `f x < f t` for some `t ∈ (x, b]`. When the sun rises far to the
right and shines horizontally over the graph of `f`, these are the points in the shadow of a later
point.

`rising_sun_lemma` (F. Riesz, 1932): if `f` is continuous on `[a, b]`, this set is open, it is
empty exactly when `f` is antitone on `[a, b]`, and otherwise it is the union of a sequence of
pairwise disjoint open intervals `(c n, d n)` with `f (c n) ≤ f (d n)` for every `n`.

## Proof outline

* The rising sun set is open: `f x < f t` persists near `x` because `f` is continuous at `x`.
* If it is empty, then `f y ≤ f x` whenever `a < x < y ≤ b`, and letting `x` tend to `a` gives
  `f y ≤ f a`. Conversely, an antitone function has no point lower than a later point.
* A bounded open set of reals is the union of a sequence of pairwise disjoint open intervals with
  endpoints outside the set: each of its points lies in such an interval, two such intervals are
  equal or disjoint, so there are countably many of them since `ℝ` is separable, and the unused
  indices get empty intervals `(c n, c n)`.
* On such an interval `(c, d)` of the rising sun set, `f t ≤ f d` for `t ∈ [d, b]` because `d`
  is not in the set. For `x ∈ (c, d)`, a maximum point `s` of `f` on `[x, b]` cannot lie in
  `(c, d)`, where every point is lower than a later one, so `s ≥ d` and `f x ≤ f s ≤ f d`.
  Letting `x` tend to `c` gives `f c ≤ f d`.

## Implementation notes

The definitions `risingSunSet`, `HasRisingSunDecomposition` and `HasRisingSunProperty` and the
statement keep the full names they had in the former wanted module, so the namespace still reads
`RisingSunWanted` and repeats `Analysis`; the `dupNamespace` linter is turned off for these four
declarations only.

The hypothesis `a < b` of `rising_sun_lemma` is part of that statement but is not used: when
`b ≤ a`, the rising sun set is empty and `[a, b]` has at most one point, so the property holds
trivially. The `unusedVariables` linter is turned off for this theorem only.

## References

* F. Riesz (1932). Knill, §163. This is the source cited by problem `rising_sun_lemma` of the
  lean-eval benchmark (leanprover/lean-eval), from which the definitions and the statement are
  taken.
-/

@[expose] public section

namespace MathlibExt.Analysis.RisingSunWanted
namespace Analysis.RisingSun

open Set

set_option linter.dupNamespace false in
/-- Points of `(a,b)` lower than some later point. -/
def risingSunSet (a b : ℝ) (f : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ Ioo a b ∧ ∃ t ∈ Icc x b, x < t ∧ f x < f t}

set_option linter.dupNamespace false in
/-- A countable disjoint open-interval decomposition with the endpoint
inequality `f(c_n) ≤ f(d_n)`. -/
def HasRisingSunDecomposition (E : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ c d : ℕ → ℝ,
    E = ⋃ n : ℕ, Ioo (c n) (d n) ∧
    (Set.PairwiseDisjoint (Set.univ : Set ℕ) fun n => Ioo (c n) (d n)) ∧
    ∀ n : ℕ, f (c n) ≤ f (d n)

set_option linter.dupNamespace false in
/-- The rising-sun property on `[a,b]`. -/
def HasRisingSunProperty (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  IsOpen (risingSunSet a b f) ∧
  (risingSunSet a b f = ∅ ↔ AntitoneOn f (Icc a b)) ∧
  ((risingSunSet a b f).Nonempty → HasRisingSunDecomposition (risingSunSet a b f) f)

/-- Two open intervals contained in `U`, with endpoints outside `U`, that meet are equal. -/
private lemma eq_of_Ioo_subset_of_notMem {U : Set ℝ} {c d c' d' z : ℝ}
    (hsub : Ioo c d ⊆ U) (hc : c ∉ U) (hd : d ∉ U) (hsub' : Ioo c' d' ⊆ U) (hc' : c' ∉ U)
    (hd' : d' ∉ U) (hz : z ∈ Ioo c d) (hz' : z ∈ Ioo c' d') : c = c' ∧ d = d' := by
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · exact not_lt.1 fun h => hc (hsub' ⟨h, hz.1.trans hz'.2⟩)
  · exact not_lt.1 fun h => hc' (hsub ⟨h, hz'.1.trans hz.2⟩)
  · exact not_lt.1 fun h => hd' (hsub ⟨hz.1.trans hz'.2, h⟩)
  · exact not_lt.1 fun h => hd (hsub' ⟨hz'.1.trans hz.2, h⟩)

/-- Each point of a bounded open set of reals lies in an open interval contained in the set,
with endpoints outside the set. -/
private lemma exists_Ioo_of_mem {U : Set ℝ} (hU : IsOpen U) (hbl : BddBelow U)
    (hba : BddAbove U) {x : ℝ} (hx : x ∈ U) :
    ∃ c d, c < d ∧ Ioo c d ⊆ U ∧ c ∉ U ∧ d ∉ U ∧ x ∈ Ioo c d := by
  obtain ⟨m, hm⟩ := hbl
  obtain ⟨M, hM⟩ := hba
  -- the closed sets of points outside `U`, to the left and to the right of `x`
  let L := {y | y ≤ x ∧ y ∉ U}
  let R := {y | x ≤ y ∧ y ∉ U}
  have hLne : L.Nonempty := ⟨min x (m - 1), min_le_left _ _, fun h =>
    (sub_one_lt m).not_ge ((hm h).trans (min_le_right _ _))⟩
  have hRne : R.Nonempty := ⟨max x (M + 1), le_max_left _ _, fun h =>
    (lt_add_one M).not_ge ((le_max_right _ _).trans (hM h))⟩
  have hLb : BddAbove L := ⟨x, fun y hy => hy.1⟩
  have hRb : BddBelow R := ⟨x, fun y hy => hy.1⟩
  obtain ⟨hcx, hcU⟩ := (isClosed_Iic.inter hU.isClosed_compl).csSup_mem hLne hLb
  obtain ⟨hxd, hdU⟩ := (isClosed_Ici.inter hU.isClosed_compl).csInf_mem hRne hRb
  have hcx' : sSup L < x := hcx.lt_of_ne fun h => hcU (by rwa [h])
  have hxd' : x < sInf R := hxd.lt_of_ne fun h => hdU (by rwa [← h])
  refine ⟨sSup L, sInf R, hcx'.trans hxd', fun z hz => ?_, hcU, hdU, hcx', hxd'⟩
  by_contra hzU
  rcases le_total z x with hzx | hxz
  · exact (le_csSup hLb ⟨hzx, hzU⟩).not_gt hz.1
  · exact (csInf_le hRb ⟨hxz, hzU⟩).not_gt hz.2

/-- A bounded open set of reals is the union of a sequence of pairwise disjoint open intervals,
each of which is empty with equal endpoints or has its endpoints outside the set. -/
private lemma exists_seq_Ioo_of_isOpen {U : Set ℝ} (hU : IsOpen U) (hbl : BddBelow U)
    (hba : BddAbove U) :
    ∃ c d : ℕ → ℝ, U = ⋃ n, Ioo (c n) (d n) ∧
      (univ : Set ℕ).PairwiseDisjoint (fun n => Ioo (c n) (d n)) ∧
      ∀ n, c n = d n ∨ (c n < d n ∧ c n ∉ U ∧ d n ∉ U) := by
  -- the pairs of endpoints of the intervals making up `U`
  let T : Set (ℝ × ℝ) := {p | p.1 < p.2 ∧ Ioo p.1 p.2 ⊆ U ∧ p.1 ∉ U ∧ p.2 ∉ U}
  have hdisj : T.PairwiseDisjoint fun p => Ioo p.1 p.2 := by
    rintro p ⟨-, hsub, hc, hd⟩ q ⟨-, hsub', hc', hd'⟩ hpq
    refine disjoint_left.2 fun z hz hz' => hpq ?_
    obtain ⟨h1, h2⟩ := eq_of_Ioo_subset_of_notMem hsub hc hd hsub' hc' hd' hz hz'
    exact Prod.ext h1 h2
  have hTc : T.Countable :=
    hdisj.countable_of_isOpen (fun _ _ => isOpen_Ioo) fun p hp => nonempty_Ioo.2 hp.1
  -- enumerate `T` without repetition, padding with the empty interval `(0, 0)`
  let _ : Encodable T := hTc.toEncodable
  let g : ℕ → ℝ × ℝ := fun n => ((Encodable.decode₂ T n).map Subtype.val).getD (0, 0)
  have hg : ∀ n, g n = (0, 0) ∨ ∃ p : T, Encodable.encode p = n ∧ g n = p := by
    intro n
    cases h : Encodable.decode₂ T n with
    | none => exact Or.inl (by simp [g, h])
    | some p => exact Or.inr ⟨p, Encodable.mem_decode₂.1 h, by simp [g, h]⟩
  refine ⟨fun n => (g n).1, fun n => (g n).2, ?_, ?_, fun n => ?_⟩
  · ext x
    simp only [mem_iUnion]
    refine ⟨fun hx => ?_, fun ⟨n, hn⟩ => ?_⟩
    · obtain ⟨c, d, hcd, hsub, hc, hd, hxcd⟩ := exists_Ioo_of_mem hU hbl hba hx
      exact ⟨Encodable.encode (⟨(c, d), hcd, hsub, hc, hd⟩ : T), by simpa [g] using hxcd⟩
    · rcases hg n with h | ⟨p, -, h⟩
      · simp [h] at hn
      · rw [h] at hn
        exact p.2.2.1 hn
  · intro n _ k _ hnk
    rcases hg n with hn | ⟨p, hpn, hn⟩
    · simp [Function.onFun, hn]
    rcases hg k with hk | ⟨q, hqk, hk⟩
    · simp [Function.onFun, hk]
    have hpq : (p : ℝ × ℝ) ≠ q := fun h => hnk (hpn ▸ hqk ▸ congrArg _ (Subtype.ext h))
    simpa [Function.onFun, hn, hk] using hdisj p.2 q.2 hpq
  · rcases hg n with hn | ⟨p, -, hn⟩
    · exact Or.inl (by simp [hn])
    · exact Or.inr (by simpa [hn] using ⟨p.2.1, p.2.2.2.1, p.2.2.2.2⟩)

/-- The rising sun set of a function continuous on `[a, b]` is open. -/
private lemma isOpen_risingSunSet {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    IsOpen (risingSunSet a b f) := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨hx, t, ht, hxt, hft⟩ => ?_
  have hcont : ContinuousAt f x := hf.continuousAt (Icc_mem_nhds hx.1 hx.2)
  filter_upwards [Ioo_mem_nhds hx.1 hx.2, Iio_mem_nhds hxt,
    hcont.tendsto.eventually (eventually_lt_nhds hft)] with y hy hyt hfy
  exact ⟨hy, t, ⟨hyt.le, ht.2⟩, hyt, hfy⟩

/-- The rising sun set of a function continuous on `[a, b]` is empty exactly when the function
is antitone on `[a, b]`. -/
private lemma risingSunSet_eq_empty_iff {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    risingSunSet a b f = ∅ ↔ AntitoneOn f (Icc a b) := by
  refine ⟨fun h x hx y hy hxy => ?_, fun h => ?_⟩
  · have hnot : ∀ z ∈ Ioo a b, ∀ t ∈ Icc z b, z < t → f t ≤ f z := fun z hz t ht hzt =>
      not_lt.1 fun hlt => eq_empty_iff_forall_notMem.1 h z ⟨hz, t, ht, hzt, hlt⟩
    rcases hxy.eq_or_lt with rfl | hxy
    · exact le_rfl
    rcases hx.1.eq_or_lt with rfl | hax
    · -- `f y ≤ f z` for `z ∈ (a, y)`; let `z` tend to `a`
      refine ContinuousWithinAt.closure_le (s := Ioo a y) ?_ continuousWithinAt_const
        ((hf a hx).mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc_right hy.2))) fun z hz =>
          hnot z ⟨hz.1, hz.2.trans_le hy.2⟩ y ⟨hz.2.le, hy.2⟩ hz.2
      rw [closure_Ioo hxy.ne]
      exact left_mem_Icc.2 hxy.le
    · exact hnot x ⟨hax, hxy.trans_le hy.2⟩ y ⟨hxy.le, hy.2⟩ hxy
  · refine eq_empty_iff_forall_notMem.2 fun x ⟨hx, t, ht, hxt, hft⟩ => ?_
    exact (h ⟨hx.1.le, hx.2.le⟩ ⟨hx.1.le.trans hxt.le, ht.2⟩ hxt.le).not_gt hft

/-- If `(c, d)` is a nonempty open interval contained in the rising sun set of a function `f`
continuous on `[a, b]`, and `d` is not in that set, then `f c ≤ f d`. -/
private lemma le_of_Ioo_subset_risingSunSet {a b c d : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hcd : c < d) (hsub : Ioo c d ⊆ risingSunSet a b f)
    (hd : d ∉ risingSunSet a b f) : f c ≤ f d := by
  obtain ⟨hac, hdb⟩ := (Ioo_subset_Ioo_iff hcd).1 (hsub.trans fun x hx => hx.1)
  -- no point of `(d, b]` is higher than `d`
  have hright : ∀ t ∈ Icc d b, f t ≤ f d := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hdt
    · exact le_rfl
    exact not_lt.1 fun hlt =>
      hd ⟨⟨hac.trans_lt hcd, hdt.trans_le ht.2⟩, t, ⟨hdt.le, ht.2⟩, hdt, hlt⟩
  -- a maximum point of `f` on `[x, b]` lies in `[d, b]`
  have hmid : ∀ x ∈ Ioo c d, f x ≤ f d := by
    intro x hx
    have hxb : x ∈ Icc x b := left_mem_Icc.2 (hx.2.le.trans hdb)
    obtain ⟨s, hs, hsmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x, hxb⟩
      (hf.mono (Icc_subset_Icc_left (hac.trans hx.1.le)))
    rw [isMaxOn_iff] at hsmax
    rcases lt_or_ge s d with hsd | hds
    · obtain ⟨-, t, ht, hst, hfst⟩ := hsub ⟨hx.1.trans_le hs.1, hsd⟩
      exact absurd (hsmax t ⟨hs.1.trans ht.1, ht.2⟩) hfst.not_ge
    · exact (hsmax x hxb).trans (hright s ⟨hds, hs.2⟩)
  -- let `x` tend to `c`
  refine ContinuousWithinAt.closure_le (s := Ioo c d) ?_
    ((hf c ⟨hac, hcd.le.trans hdb⟩).mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc hac hdb)))
    continuousWithinAt_const hmid
  rw [closure_Ioo hcd.ne]
  exact left_mem_Icc.2 hcd.le

/- **Riesz's rising sun lemma.** Every continuous real function on a compact
interval has the rising-sun property. -/
set_option linter.dupNamespace false in
set_option linter.unusedVariables false in
/-- Source: F. Riesz (1932). Knill, §163. Via leanprover/lean-eval@38361be, problem
`rising_sun_lemma`. -/
theorem rising_sun_lemma {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    HasRisingSunProperty a b f := by
  refine ⟨isOpen_risingSunSet hf, risingSunSet_eq_empty_iff hf, fun _ => ?_⟩
  obtain ⟨c, d, hU, hdisj, hend⟩ := exists_seq_Ioo_of_isOpen (isOpen_risingSunSet hf)
    (bddBelow_Ioo.mono fun x hx => hx.1) (bddAbove_Ioo.mono fun x hx => hx.1)
  refine ⟨c, d, hU, hdisj, fun n => ?_⟩
  rcases hend n with h | ⟨hcd, -, hd⟩
  · rw [h]
  · refine le_of_Ioo_subset_risingSunSet hf hcd ?_ hd
    rw [hU]
    exact subset_iUnion (fun n => Ioo (c n) (d n)) n

end Analysis.RisingSun

end MathlibExt.Analysis.RisingSunWanted
