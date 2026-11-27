/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Independent sets of set mappings on pairs

We prove that the largest guaranteed size of an independent set is of order
$\sqrt{n}$. The lower bound counts forbidden triples in a uniformly sized sample.
The upper bound uses the Conlon–Fox–Sudakov grid construction for pairs.

See D. Conlon, J. Fox and B. Sudakov, *Short proofs of some extremal results II*,
[Section 2](https://arxiv.org/abs/1507.00547).

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/PairSetMappingIndependenceErdosProblem1025Wanted.lean`:

Source: T. F. Bloom, Erdős Problems, Problem #1025, https://www.erdosproblems.com/1025 (status
SOLVED (LEAN)). UnsolvedMath record UM-30007132 (`EP-1025`), dataset ulamai/UnsolvedMath v1.8.0.

Pairs are unordered pairs of distinct elements (`Sym2`, diagonal values unused); `g(n)` is the
largest guaranteed size. For `n = 2` no admissible mapping exists, so every `k` qualifies and `sSup`
returns the junk value `0`; `IsTheta` at `atTop` ignores it. The estimate is stated as
`g(n) ≍ n^{1/2}` (`Asymptotics.IsTheta`): Spencer's Turán bound for `3`-graphs gives the lower
bound, and Conlon, Fox and Sudakov (Section 2, Theorem 2.1 with `k = 2`, `l = 1`) give the upper
bound. The UnsolvedMath triage note proposed `(n log n)^{1/2}`, which is only the upper bound of
Erdős and Hajnal. Compared with the formal-conjectures statement `ErdosProblems/1025.lean`
(equivalent; no code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025Wanted

/-- **Independent set of a set mapping on pairs.** Let $n$ be a natural number and let $f$ assign
to each unordered pair $\{x, y\}$ of elements of $\{0, \dots, n-1\}$ (possibly with $x = y$) an
element of $\{0, \dots, n-1\}$. A finite set $X \subseteq \{0, \dots, n-1\}$ is independent for $f$
if $f(\{x, y\}) \notin X$ for all distinct $x, y \in X$.
-/
def IsIndependentFor {n : ℕ} (f : Sym2 (Fin n) → Fin n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f s(x, y) ∉ X

/-- **Independence number of set mappings on pairs.** For a natural number $n$, $g(n)$ is the
largest $k$ such that every map $f$ from the unordered pairs $\{x, y\}$ of elements of
$\{0, \dots, n-1\}$ (possibly with $x = y$) to $\{0, \dots, n-1\}$ with
$f(\{x, y\}) \notin \{x, y\}$ for all distinct $x, y$ has an independent set of at least $k$
elements, that is, a set $X \subseteq \{0, \dots, n-1\}$ with $|X| \ge k$ and
$f(\{x, y\}) \notin X$ for all distinct $x, y \in X$. If no largest such $k$ exists, $g(n) = 0$;
this happens for $n = 2$, where no such $f$ exists. -/
noncomputable def setMappingIndependence (n : ℕ) : ℕ :=
  sSup {k | ∀ f : Sym2 (Fin n) → Fin n, (∀ x y, x ≠ y → f s(x, y) ≠ x ∧ f s(x, y) ≠ y) →
    ∃ X : Finset (Fin n), IsIndependentFor f X ∧ k ≤ X.card}

/-- **Statement of Erdős Problem 1025.** For a natural number $n$, let $g(n)$ be the largest $k$
such that every map $f$ from the unordered pairs of elements of $\{0, \dots, n-1\}$ to
$\{0, \dots, n-1\}$ with $f(\{x, y\}) \notin \{x, y\}$ for all distinct $x, y$ admits a set $X$
of at least $k$ elements with $f(\{x, y\}) \notin X$ for all distinct $x, y \in X$ (and
$g(n) = 0$ if no largest such $k$ exists). This is the proposition that $g(n) \asymp \sqrt{n}$ as
$n \to \infty$, that is, that there are constants $c, C > 0$ with
$c \sqrt{n} \le g(n) \le C \sqrt{n}$ for all sufficiently large $n$.

Spencer proved the lower bound and Conlon, Fox and Sudakov the upper bound. -/
def setMappingIndependenceAsymp : Prop :=
  Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (setMappingIndependence n : ℝ))
    (fun n : ℕ => Real.sqrt n)

open Finset

private abbrev Admissible {n : ℕ} (f : Sym2 (Fin n) → Fin n) :=
  ∀ x y, x ≠ y → f s(x, y) ≠ x ∧ f s(x, y) ≠ y

-- Sampling 2r vertices costs at most r deletions on average.
private lemma sampling_bound {n r : ℕ} (hr : 2 ≤ r) (hn : 64 * r ^ 2 ≤ n) :
    n * n * (n - 3).choose (2 * r - 3) ≤ n.choose (2 * r) * r := by
  have hn4 : 4 ≤ n := by nlinarith
  have triple (a : ℕ) : 6 * a.choose 3 = (a - 2) * (a - 1) * a := by
    simpa [Nat.descFactorial_succ, Nat.factorial, mul_assoc] using
      (Nat.descFactorial_eq_factorial_mul_choose a 3).symm
  have small : 6 * (2 * r).choose 3 ≤ 8 * r ^ 3 := by
    rw [triple]
    calc
      _ ≤ (2 * r) * (2 * r) * (2 * r) := by gcongr <;> omega
      _ = _ := by ring
  have large : n * n * n ≤ 4 * (6 * n.choose 3) := by
    rw [triple]
    calc
      _ ≤ (2 * (n - 2)) * (2 * (n - 1)) * n := by gcongr <;> omega
      _ = _ := by ring
  have ratio : n * n * (2 * r).choose 3 ≤ n.choose 3 * r := by
    have h := calc
      4 * (n * n) * (6 * (2 * r).choose 3) ≤ 4 * (n * n) * (8 * r ^ 3) := by gcongr
      _ = n * n * (32 * r ^ 2) * r := by ring
      _ ≤ n * n * n * r := by gcongr; omega
      _ ≤ 4 * (6 * n.choose 3) * r := by gcongr
    nlinarith only [h]
  refine Nat.le_of_mul_le_mul_left (c := n.choose 3) ?_ (Nat.choose_pos (by omega))
  calc
    _ = n * n * (n.choose (2 * r) * (2 * r).choose 3) := by
      rw [Nat.choose_mul (s := 3) (by omega : 3 ≤ 2 * r)]
      ring
    _ = n.choose (2 * r) * (n * n * (2 * r).choose 3) := by ring
    _ ≤ n.choose (2 * r) * (n.choose 3 * r) := by gcongr
    _ = _ := by ring

private lemma exists_independent {n r : ℕ} (hr : 2 ≤ r) (hn : 64 * r ^ 2 ≤ n)
    (f : Sym2 (Fin n) → Fin n) (hf : Admissible f) :
    ∃ X : Finset (Fin n), IsIndependentFor f X ∧ r ≤ X.card := by
  classical
  let samples := (univ : Finset (Fin n)).powersetCard (2 * r)
  let triple (p : Fin n × Fin n) : Finset (Fin n) := {p.1, p.2, f s(p.1, p.2)}
  let bad (X : Finset (Fin n)) (p : Fin n × Fin n) := p.1 ≠ p.2 ∧ triple p ⊆ X
  have degree (p : Fin n × Fin n) :
      (samples.bipartiteBelow bad p).card ≤ (n - 3).choose (2 * r - 3) := by
    by_cases hp : p.1 = p.2
    · simp [bipartiteBelow, bad, hp]
    have ht : (triple p).card = 3 :=
      card_triple_eq_three_iff.mpr ⟨hp, (hf _ _ hp).1.symm, (hf _ _ hp).2.symm⟩
    simpa [bipartiteBelow, bad, hp, samples, ht] using
      (card_filter_powersetCard_subset (triple p) univ (2 * r) (subset_univ _)
        (by rw [ht]; omega)).le
  have hsize : 2 * r ≤ n := by nlinarith
  obtain ⟨X, hX, hbad⟩ : ∃ X ∈ samples, (univ.bipartiteAbove bad X).card ≤ r := by
    by_contra! h
    have hc := card_nsmul_lt_card_nsmul_of_lt_of_le (R := ℕ) bad
      (s := samples) (t := univ) (powersetCard_nonempty.mpr (by simpa using hsize))
      h (fun p _ ↦ degree p)
    apply (sampling_bound hr hn).not_gt
    simpa [samples, card_powersetCard] using hc
  let outputs := (univ.bipartiteAbove bad X).image fun p ↦ f s(p.1, p.2)
  refine ⟨X \ outputs, ?_, ?_⟩
  · intro x hx y hy hxy hz
    have hsub : triple (x, y) ⊆ X := by
      simp only [triple, insert_subset_iff, singleton_subset_iff]
      exact ⟨(mem_sdiff.mp hx).1, (mem_sdiff.mp hy).1, (mem_sdiff.mp hz).1⟩
    exact (mem_sdiff.mp hz).2 (mem_image.mpr
      ⟨(x, y), (mem_bipartiteAbove _).mpr ⟨mem_univ _, hxy, hsub⟩, rfl⟩)
  · have hcard := (mem_powersetCard.mp hX).2
    have hrem := card_le_card_sdiff_add_card (s := X) (t := outputs)
    have hout : outputs.card ≤ r := card_image_le.trans hbad
    omega

-- In different rows, take the corner in the earlier row and the later point's column.
-- If the corner is unavailable or is an endpoint, choose any point outside the pair.
private lemma exists_grid_map {n q : ℕ} (hn : 3 ≤ n) (e : Fin n ↪ Fin q × Fin q) :
    ∃ f : Sym2 (Fin n) → Fin n, Admissible f ∧
      ∀ x y z, (e x).1 < (e y).1 → e z = ((e x).1, (e y).2) →
        z ≠ x → z ≠ y → f s(x, y) = z := by
  classical
  let corner : Sym2 (Fin n) → Fin q × Fin q := Sym2.lift
    ⟨fun x y ↦ if (e x).1 < (e y).1 then ((e x).1, (e y).2)
      else if (e y).1 < (e x).1 then ((e y).1, (e x).2) else e x ⊓ e y, by
        intro x y
        rcases lt_trichotomy (e x).1 (e y).1 with h | h | h
        · simp [h, h.asymm]
        · simp [h, inf_comm]
        · simp [h, h.asymm]⟩
  have outside (p : Sym2 (Fin n)) : ∃ z : Fin n, z ∉ p := by
    have hcard : p.toFinset.card < (univ : Finset (Fin n)).card := by
      rw [Sym2.card_toFinset]
      split <;> simp <;> omega
    obtain ⟨z, _, hz⟩ := exists_mem_notMem_of_card_lt_card hcard
    exact ⟨z, fun h ↦ hz (Sym2.mem_toFinset.mpr h)⟩
  let f (p : Sym2 (Fin n)) :=
    if h : ∃ z, z ∉ p ∧ e z = corner p then h.choose else (outside p).choose
  refine ⟨f, ?_, ?_⟩
  · have avoids (p : Sym2 (Fin n)) : f p ∉ p := by
      dsimp only [f]
      split
      · rename_i h
        exact h.choose_spec.1
      · exact (outside p).choose_spec
    intro x y _
    simpa [Sym2.mem_iff] using avoids s(x, y)
  · intro x y z hrow hz hzx hzy
    have h : ∃ w, w ∉ s(x, y) ∧ e w = corner s(x, y) := by
      exact ⟨z, by simp [Sym2.mem_iff, hzx, hzy], by simpa [corner, hrow] using hz⟩
    apply e.injective
    dsimp only [f]
    rw [dite_eq_left h, h.choose_spec.2, hz]
    simp [corner, hrow]

private lemma grid_independent_card {n q : ℕ} (e : Fin n ↪ Fin q × Fin q)
    {f : Sym2 (Fin n) → Fin n}
    (hcorner : ∀ x y z, (e x).1 < (e y).1 → e z = ((e x).1, (e y).2) →
      z ≠ x → z ≠ y → f s(x, y) = z)
    {X : Finset (Fin n)} (hX : IsIndependentFor f X) : X.card ≤ 2 * q := by
  classical
  let alone (x : Fin n) := ∀ y ∈ X, (e y).1 = (e x).1 → y = x
  -- Singleton rows contribute at most q points.
  have hrows : (X.filter alone).card ≤ q := by
    have h := card_le_card_of_injOn (t := univ) (fun x ↦ (e x).1)
      (fun _ _ ↦ mem_univ _) (s := X.filter alone) (by
        intro x hx y hy he
        exact (mem_filter.mp hy).2 x (mem_filter.mp hx).1 he)
    simpa using h
  -- In every other row, each point must be the last in its column.
  have last {x y : Fin n} (hx : x ∈ X.filter (fun z ↦ ¬alone z)) (hy : y ∈ X)
      (hcol : (e x).2 = (e y).2) : (e y).1 ≤ (e x).1 := by
    by_contra! hlt
    obtain ⟨z, hz, hrow, hne⟩ : ∃ z ∈ X, (e z).1 = (e x).1 ∧ z ≠ x := by
      simpa [alone] using (mem_filter.mp hx).2
    have hzy : (e z).1 < (e y).1 := hrow ▸ hlt
    have hxy : x ≠ y := fun he ↦ hlt.ne (congrArg (fun a ↦ (e a).1) he)
    have heq := hcorner z y x hzy (Prod.ext hrow.symm hcol) hne.symm hxy
    exact hX z hz y hy (fun he ↦ hzy.ne (congrArg (fun a ↦ (e a).1) he))
      (heq ▸ (mem_filter.mp hx).1)
  have hcols : (X.filter (fun z ↦ ¬alone z)).card ≤ q := by
    have h := card_le_card_of_injOn (t := univ) (fun x ↦ (e x).2)
      (fun _ _ ↦ mem_univ _) (s := X.filter (fun z ↦ ¬alone z)) (by
        intro x hx y hy he
        exact e.injective (Prod.ext
          (le_antisymm (last hy (mem_filter.mp hx).1 he.symm) (last hx (mem_filter.mp hy).1 he))
          he))
    simpa using h
  have := card_filter_add_card_filter_not (s := X) alone
  omega

private lemma independence_bounds {n : ℕ} (hn : 256 ≤ n) :
    n.sqrt / 8 ≤ setMappingIndependence n ∧ setMappingIndependence n ≤ 2 * (n.sqrt + 1) := by
  let q := n.sqrt + 1
  let e : Fin n ↪ Fin q × Fin q :=
    (Fin.castLEEmb (Nat.lt_succ_sqrt n).le).trans finProdFinEquiv.symm.toEmbedding
  obtain ⟨f, hf, hcorner⟩ := exists_grid_map (by omega : 3 ≤ n) e
  have hub : ∀ k ∈ {k | ∀ g : Sym2 (Fin n) → Fin n, Admissible g →
      ∃ X : Finset (Fin n), IsIndependentFor g X ∧ k ≤ X.card}, k ≤ 2 * q := by
    intro k hk
    obtain ⟨X, hX, hkX⟩ := hk f hf
    exact hkX.trans (grid_independent_card e hcorner hX)
  refine ⟨le_csSup ⟨_, hub⟩ ?_, csSup_le' hub⟩
  have hs : 16 ≤ n.sqrt := Nat.le_sqrt.mpr hn
  have hmul : 8 * (n.sqrt / 8) ≤ n.sqrt := by omega
  exact exists_independent (by omega) (by
    calc
      64 * (n.sqrt / 8) ^ 2 = (8 * (n.sqrt / 8)) * (8 * (n.sqrt / 8)) := by ring
      _ ≤ n.sqrt * n.sqrt := by gcongr
      _ ≤ n := Nat.sqrt_le n)

/-- **Erdős Problem 1025 (Spencer; Conlon, Fox and Sudakov).** For a natural number $n$, let $g(n)$
be the largest $k$ such that every map $f$ from the unordered pairs of elements of
$\{0, \dots, n-1\}$ to $\{0, \dots, n-1\}$ with $f(\{x, y\}) \notin \{x, y\}$ for all distinct
$x, y$ admits a set $X$ of at least $k$ elements with $f(\{x, y\}) \notin X$ for all distinct
$x, y \in X$ (and $g(n) = 0$ if no largest such $k$ exists). Then there are constants $c, C > 0$
such that $c \sqrt{n} \le g(n) \le C \sqrt{n}$ for all sufficiently large $n$, that is,
$g(n) \asymp \sqrt{n}$ as $n \to \infty$.

Source: T. F. Bloom, Erdős Problems, Problem #1025,
https://www.erdosproblems.com/1025 (status SOLVED (LEAN)); resolution: J. Spencer, Turán's theorem
for k-graphs, Discrete Math. (1972), 183-186; D. Conlon, J. Fox and B. Sudakov, Short proofs of some
extremal results II, J. Combin. Theory Ser. B (2016), 173-196, Spencer: g(n) ≫ n^{1/2};
Conlon-Fox-Sudakov: g(n) ≪ n^{1/2} (erdosproblems.com/1025),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1025.lean#L829.
-/
theorem setMappingIndependenceAsymp_holds : setMappingIndependenceAsymp := by
  constructor
  · refine Asymptotics.isBigO_iff.mpr ⟨4, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 256] with n hn
    simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hupper : (setMappingIndependence n : ℝ) ≤ 2 * ((n.sqrt : ℝ) + 1) := by
      exact_mod_cast (independence_bounds hn).2
    have hs : (n.sqrt : ℝ) ≤ Real.sqrt n :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
    have hone : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by omega)
    linarith [show (1 : ℝ) ≤ n.sqrt by exact_mod_cast hone]
  · refine Asymptotics.isBigO_iff.mpr ⟨16, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 256] with n hn
    simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : Real.sqrt n ≤ (n.sqrt : ℝ) + 1 := by
      apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      exact_mod_cast (Nat.lt_succ_sqrt' n).le
    have hlow := (independence_bounds hn).1
    have h16 : 16 ≤ n.sqrt := Nat.le_sqrt.mpr hn
    have : n.sqrt + 1 ≤ 16 * setMappingIndependence n := by omega
    exact hs.trans (by exact_mod_cast this)

end MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025Wanted
