/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Meromorphic.Divisor
public import MathlibExt.Analysis.SpecialFunctions.Elliptic.Function
public import MathlibExt.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogram

/-!
# Pole sets and elliptic order of meromorphic elliptic functions

For an elliptic function `f` relative to a period pair `L`, this module provides:

* `PeriodPair.poleMultiplicity`, the pointwise pole multiplicity, defined locally from
  `meromorphicOrderAt f z` as the negation (truncated to `ℕ`) of the order. No global
  meromorphicity hypothesis is built into the definition: at points where `f` is not
  even locally meromorphic, the order takes the junk value `0`, so the multiplicity
  is `0` there for an explicitly local reason.
* `PeriodPair.poleSetInFundamentalParallelogram`, the set of poles of `f` lying in
  the fundamental parallelogram with vertex `α`. The parallelogram uses the half-open
  convention `0 ≤ tᵢ < 1` (see `PeriodPair.mem_fundamentalParallelogram_iff`), so the
  vertex `α` belongs to it while the translates `α + ω₁`, `α + ω₂`, `α + ω₁ + ω₂`
  do not.
* `PeriodPair.ellipticOrderInFundamentalParallelogram`, the sum of the pole
  multiplicities over that set, for an arbitrary vertex `α`.
* `PeriodPair.ellipticOrder`, the canonical order at vertex `0`, with an unfolding
  bridge to the arbitrary-vertex count. No independence of the vertex is claimed.
-/

@[expose] public section

namespace PeriodPair

/-- **Pole multiplicity.** For a function $f : \mathbb{C} \to \mathbb{C}$ and a point
$z \in \mathbb{C}$, let $\operatorname{ord}_z f \in \mathbb{Z} \cup \{\infty\}$ be the meromorphic
order of $f$ at $z$, which by convention is $0$ when $f$ is not meromorphic at $z$. The pole
multiplicity of $f$ at $z$ is the natural number $\max(0, -\operatorname{ord}_z f)$ when
$\operatorname{ord}_z f$ is finite, and $0$ when $\operatorname{ord}_z f = \infty$. Thus a pole of
order $n \ge 1$ has multiplicity $n$, and every point of nonnegative or infinite order, including
every point where $f$ is not meromorphic, has multiplicity $0$.

Only the order at $z$ is used, so the value at $z$ depends only on the behavior of $f$ near $z$.
-/
noncomputable def poleMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  (-(meromorphicOrderAt f z).untop₀).toNat

/-- **Pole multiplicity vanishes where the function is not meromorphic.** Let
$f \colon \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$. If $f$ is not meromorphic at $z$, then
the pole multiplicity of $f$ at $z$ is $0$.

This holds because the order of $f$ at such a point is $0$ by convention; no global hypothesis on
$f$ is used. -/
theorem poleMultiplicity_eq_zero_of_not_meromorphicAt {f : ℂ → ℂ} {z : ℂ}
    (h : ¬MeromorphicAt f z) : poleMultiplicity f z = 0 := by
  rw [poleMultiplicity, meromorphicOrderAt_of_not_meromorphicAt h]
  rfl

/-- **Pole multiplicity vanishes at points of nonnegative order.** Let
$f \colon \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$, and let the order of $f$ at $z$ be its
meromorphic order, an element of $\mathbb{Z} \cup \{\infty\}$ that is $0$ by convention when $f$
is not meromorphic at $z$. If this order is nonnegative (possibly $\infty$), then the pole
multiplicity of $f$ at $z$ is $0$. -/
theorem poleMultiplicity_eq_zero_of_nonneg {f : ℂ → ℂ} {z : ℂ}
    (h : 0 ≤ meromorphicOrderAt f z) : poleMultiplicity f z = 0 := by
  unfold poleMultiplicity
  cases h' : meromorphicOrderAt f z with
  | top => simp
  | coe n =>
    rw [WithTop.untop₀_coe]
    exact Int.toNat_eq_zero.mpr (neg_nonpos.mpr (by exact_mod_cast h' ▸ h))

/-- **Pole multiplicity is nonzero exactly at negative order.** Let
$f \colon \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$, and let the order of $f$ at $z$ be its
meromorphic order, an element of $\mathbb{Z} \cup \{\infty\}$ that is $0$ by convention when $f$
is not meromorphic at $z$. The pole multiplicity of $f$ at $z$ is nonzero if and only if this
order is negative, that is, if and only if $f$ has a pole at $z$.

No hypothesis on $f$ is needed: where $f$ is not meromorphic at $z$, its order is $0$ and both
sides are false. -/
theorem poleMultiplicity_ne_zero_iff {f : ℂ → ℂ} {z : ℂ} :
    poleMultiplicity f z ≠ 0 ↔ meromorphicOrderAt f z < 0 := by
  constructor
  · intro hne
    by_contra hge
    push Not at hge
    exact hne (poleMultiplicity_eq_zero_of_nonneg hge)
  · intro hlt hcon
    unfold poleMultiplicity at hcon
    rw [Int.toNat_eq_zero] at hcon
    have hle : (0 : ℤ) ≤ (meromorphicOrderAt f z).untop₀ := neg_nonpos.mp hcon
    have htop : meromorphicOrderAt f z ≠ ⊤ := ne_top_of_lt hlt
    have hcoe : ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) =
        meromorphicOrderAt f z :=
      WithTop.coe_untop₀_of_ne_top htop
    have hle' : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      hcoe ▸ (by exact_mod_cast hle)
    exact not_lt_of_ge hle' hlt

/-- **Pole multiplicity via the divisor.** Let $U \subseteq \mathbb{C}$, let
$f \colon \mathbb{C} \to \mathbb{C}$ be meromorphic on $U$ and let $z \in U$. Let $D(z)$ be the
value at $z$ of the divisor of $f$ on $U$, that is, the order of $f$ at $z$, taken to be $0$ when
that order is infinite. Then the pole multiplicity of $f$ at $z$ equals $\max(0, -D(z))$.

Unlike the divisor, the pole multiplicity is defined without reference to a domain, so no global
meromorphicity is hidden in its definition. -/
theorem poleMultiplicity_eq_neg_divisor {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : MeromorphicOn f U) (hz : z ∈ U) :
    poleMultiplicity f z = (-(MeromorphicOn.divisor f U z)).toNat := by
  rw [hf.divisor_apply hz]
  rfl

/-- **Poles in a fundamental parallelogram.** For a period pair $L$, a function
$f : \mathbb{C} \to \mathbb{C}$ and a point $\alpha \in \mathbb{C}$, the set of poles of $f$ in
the fundamental parallelogram of $L$ with vertex $\alpha$ is the set of points $z$ of that
parallelogram at which the pole multiplicity of $f$ is nonzero. -/
noncomputable def poleSetInFundamentalParallelogram (L : PeriodPair) (f : ℂ → ℂ)
    (α : ℂ) : Set ℂ :=
  {z ∈ L.fundamentalParallelogram α | poleMultiplicity f z ≠ 0}

/-- **Membership in the pole set of a fundamental parallelogram.** Let $L$ be a period pair, let
$f \colon \mathbb{C} \to \mathbb{C}$ be any function and let $\alpha, z \in \mathbb{C}$. Then $z$
lies in the pole set of $f$ in the fundamental parallelogram of $L$ with vertex $\alpha$ if and
only if $z$ lies in that parallelogram and the pole multiplicity of $f$ at $z$ is nonzero. -/
theorem mem_poleSetInFundamentalParallelogram_iff {L : PeriodPair} {f : ℂ → ℂ}
    {α z : ℂ} :
    z ∈ L.poleSetInFundamentalParallelogram f α ↔
      z ∈ L.fundamentalParallelogram α ∧ poleMultiplicity f z ≠ 0 :=
  Iff.rfl

/-- **Fundamental parallelograms are bounded.** Let $L$ be a period pair. For every
$\alpha \in \mathbb{C}$, the fundamental parallelogram of $L$ with vertex $\alpha$ is a bounded
subset of $\mathbb{C}$.

The proof covers it by the continuous image of a compact cube, rather than by an explicit norm
estimate. -/
theorem isBounded_fundamentalParallelogram (L : PeriodPair) (α : ℂ) :
    Bornology.IsBounded (L.fundamentalParallelogram α) := by
  have hsub : L.fundamentalParallelogram α ⊆
      (fun p : ℝ × ℝ => α + p.1 • L.ω₁ + p.2 • L.ω₂) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro z hz
    rw [mem_fundamentalParallelogram_iff] at hz
    obtain ⟨t₁, t₂, h1, h2, h3, h4, rfl⟩ := hz
    exact ⟨(t₁, t₂),
      ⟨Set.mem_Icc.mpr ⟨h1, le_of_lt h2⟩, Set.mem_Icc.mpr ⟨h3, le_of_lt h4⟩⟩,
      rfl⟩
  have hcont : Continuous (fun p : ℝ × ℝ => α + p.1 • L.ω₁ + p.2 • L.ω₂) := by
    fun_prop
  exact (isCompact_Icc.prod isCompact_Icc |>.image hcont).isBounded.subset hsub

/-- **Finitely many poles in a fundamental parallelogram.** Let $L$ be a period pair, let $f$ be an
elliptic function for $L$, and let $\alpha \in \mathbb{C}$. Then the set of poles of $f$ in the
fundamental parallelogram of $L$ with vertex $\alpha$ is finite.

The proof covers the parallelogram by a closed disc, on which $f$ is meromorphic, and uses that
the divisor of $f$ on that disc has finite support. -/
theorem poleSetInFundamentalParallelogram_finite (L : PeriodPair) {f : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (α : ℂ) :
    (L.poleSetInFundamentalParallelogram f α).Finite := by
  obtain ⟨R, hR⟩ := (L.isBounded_fundamentalParallelogram α).subset_closedBall 0
  have hU : MeromorphicOn f (Metric.closedBall 0 R) := hf.meromorphic.meromorphicOn
  have hfin := hU.divisor_support_finite_of_subset (isCompact_closedBall 0 R) hR
  refine hfin.subset ?_
  intro z hz
  rw [mem_poleSetInFundamentalParallelogram_iff] at hz
  obtain ⟨hzFP, hmult⟩ := hz
  have hlt : meromorphicOrderAt f z < 0 := poleMultiplicity_ne_zero_iff.mp hmult
  rw [Function.mem_support]
  rw [MeromorphicOn.divisor_apply (hU.mono_set hR) hzFP]
  intro hcon
  rw [WithTop.untop₀_eq_zero] at hcon
  rcases hcon with h0 | htop'
  · rw [h0] at hlt
    exact lt_irrefl _ hlt
  · rw [htop'] at hlt
    exact not_top_lt hlt

/-- **Elliptic order in a fundamental parallelogram.** Let $L$ be a period pair, let $f$ be an
elliptic function for $L$ and let $\alpha \in \mathbb{C}$. The elliptic order of $f$ in the
fundamental parallelogram of $L$ with vertex $\alpha$ is the natural number obtained by summing
the pole multiplicity of $f$ at $z$ over all points $z$ of the pole set of $f$ in that
parallelogram, that is, over the points of the parallelogram where this multiplicity is nonzero.
Because $f$ is elliptic, this pole set is finite, so the sum is finite. -/
noncomputable def ellipticOrderInFundamentalParallelogram (L : PeriodPair)
    (f : ℂ → ℂ) (α : ℂ) (hf : L.IsEllipticFunction f) : ℕ :=
  ∑ z ∈ (L.poleSetInFundamentalParallelogram_finite hf α).toFinset,
    poleMultiplicity f z

/-- **Elliptic order.** Let $L$ be a period pair and let $f$ be an elliptic function for $L$. The
elliptic order of $f$ is its elliptic order in the fundamental parallelogram of $L$ with vertex
$0$: the sum of the pole multiplicities of $f$ over its poles in that parallelogram. -/
noncomputable def ellipticOrder (L : PeriodPair) (f : ℂ → ℂ)
    (hf : L.IsEllipticFunction f) : ℕ :=
  L.ellipticOrderInFundamentalParallelogram f 0 hf

/-- **The elliptic order is the parallelogram order at vertex zero.** Let $L$ be a period pair
and let $f$ be an elliptic function for $L$. Then the elliptic order of $f$ equals the elliptic
order of $f$ in the fundamental parallelogram of $L$ with vertex $0$. This holds by definition. -/
@[simp]
theorem ellipticOrder_eq_orderInFundamentalParallelogram_zero (L : PeriodPair)
    {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) :
    L.ellipticOrder f hf = L.ellipticOrderInFundamentalParallelogram f 0 hf :=
  rfl

/-- **Pole multiplicity of a constant function.** For all $c, z \in \mathbb{C}$, the pole
multiplicity at $z$ of the constant function with value $c$ is $0$. This includes the zero
constant, whose meromorphic order at every point is $\infty$. -/
theorem poleMultiplicity_const (c z : ℂ) :
    poleMultiplicity (fun _ => c) z = 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [poleMultiplicity, meromorphicOrderAt_const]
  · have h : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ => c) z := by
      simp [meromorphicOrderAt_const, hc]
    exact poleMultiplicity_eq_zero_of_nonneg h

end PeriodPair

