/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# The unit vectors form a Schauder basis of `ℓ^p`

For `1 ≤ p < ∞`, the unit vectors `e i = lp.single p i 1` form a Schauder basis
of `ℓ^p (ι, 𝕜)`, with coordinate functionals given by evaluation at `i`. In
fact they form an *unconditional* Schauder basis: every `x ∈ ℓ^p` is the sum of
`x i • e i` over finite subsets of `ι`, directed by inclusion. When `ι = ℕ`
this gives the classical sequential Schauder basis, whose `n`-th partial-sum
projection is truncation to the first `n` coordinates. The projections are
contractive: their operator norms are at most `1`.

This construction complements the `L^p`-norm material in the archived `v1`
Functional Analysis book (April 6, 2021): the book defines `L^p` spaces and
proves Hölder's and Minkowski's inequalities, but does not state this basis
construction. The proof instantiates Mathlib's abstract `SchauderBasis` and
`UnconditionalSchauderBasis` structures using `lp.hasSum_single`.

## Main declarations

* `lpUnconditionalSchauderBasis` : the unit vectors as an
  `UnconditionalSchauderBasis ι 𝕜 (lp (fun _ : ι => 𝕜) p)`.
* `lpSchauderBasis` : the unit vectors as a classical
  `SchauderBasis 𝕜 (lp (fun _ : ℕ => 𝕜) p)`.
* `norm_lpSchauderBasis_proj_apply_le` : the basis projections are contractive.
* `norm_lpSchauderBasis_proj_le` : every basis projection has operator norm `≤ 1`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Lp.SchauderBasis

open scoped ENNReal

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The unit vectors form an unconditional Schauder basis of ℓᵖ.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $1 \le p < \infty$ and let $\iota$ be a type. This is the
unconditional Schauder basis of $\ell^p(\iota, \mathbb{K})$ whose $i$-th basis vector is the unit
vector $e_i$, equal to $1$ at $i$ and to $0$ elsewhere, and whose $i$-th coordinate functional is
the evaluation $x \mapsto x_i$. In particular every $x \in \ell^p(\iota, \mathbb{K})$ is the
limit in norm of the finite partial sums $\sum_{i \in A} x_i e_i$ along the finite sets
$A \subseteq \iota$ directed by inclusion. -/
noncomputable def lpUnconditionalSchauderBasis [DecidableEq ι] (hp : p ≠ ⊤) :
    UnconditionalSchauderBasis ι 𝕜 (lp (fun _ : ι => 𝕜) p) where
  basis i := lp.single p i 1
  coord i := lp.evalCLM 𝕜 (fun _ : ι => 𝕜) p i
  ortho i j := by
    have h1 : (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) p i)
        (lp.single (E := fun _ : ι => 𝕜) p j (1 : 𝕜))
        = (lp.single (E := fun _ : ι => 𝕜) p j (1 : 𝕜)) i := rfl
    rw [h1]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_eq_same]
    · simp [hij, Pi.single_eq_of_ne]
  expansion x := by
    have h : HasSum (fun i : ι => lp.single (E := fun _ : ι => 𝕜) p i (x i)) x :=
      lp.hasSum_single hp x
    have hfun : (fun i : ι => (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) p i) x • lp.single p i (1 : 𝕜))
        = fun i : ι => lp.single (E := fun _ : ι => 𝕜) p i (x i) := by
      funext i
      show (x i) • lp.single (E := fun _ : ι => 𝕜) p i (1 : 𝕜)
        = lp.single (E := fun _ : ι => 𝕜) p i (x i)
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hfun]
    exact h

/-- **The unit vectors form a Schauder basis of ℓᵖ.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $1 \le p < \infty$. This is the Schauder basis of
$\ell^p(\mathbb{N}, \mathbb{K})$ whose $i$-th basis vector is the unit vector $e_i$, equal to $1$ at
$i$ and to $0$ elsewhere, and whose $i$-th coordinate functional is the evaluation $x \mapsto x_i$.
In particular every $x \in \ell^p(\mathbb{N}, \mathbb{K})$ is the limit in norm of its partial sums
$\sum_{i < n} x_i e_i$ as $n \to \infty$. -/
noncomputable def lpSchauderBasis (hp : p ≠ ⊤) :
    SchauderBasis 𝕜 (lp (fun _ : ℕ => 𝕜) p) where
  basis i := lp.single p i 1
  coord i := lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) p i
  ortho i j := by
    have h1 : (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) p i)
        (lp.single (E := fun _ : ℕ => 𝕜) p j (1 : 𝕜))
        = (lp.single (E := fun _ : ℕ => 𝕜) p j (1 : 𝕜)) i := rfl
    rw [h1]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_eq_same]
    · simp [hij, Pi.single_eq_of_ne]
  expansion x := by
    have h : HasSum (fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) p i (x i)) x :=
      lp.hasSum_single hp x
    have hfun : (fun i : ℕ => (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) p i) x • lp.single p i (1 : 𝕜))
        = fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) p i (x i) := by
      funext i
      show (x i) • lp.single (E := fun _ : ℕ => 𝕜) p i (1 : 𝕜)
        = lp.single (E := fun _ : ℕ => 𝕜) p i (x i)
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hfun]
    exact h.mono_left SummationFilter.LeAtTop.le_atTop

/-- **Coordinate functionals of the unconditional ℓᵖ basis.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $1 \le p < \infty$ and let $\iota$ be a type. For every $i \in \iota$ and every
$x \in \ell^p(\iota, \mathbb{K})$, the $i$-th coordinate functional of the unconditional Schauder
basis of $\ell^p(\iota, \mathbb{K})$ by unit vectors sends $x$ to its entry $x_i$. -/
@[simp]
theorem lpUnconditionalSchauderBasis_coord_apply [DecidableEq ι] (hp : p ≠ ⊤)
    (i : ι) (x : lp (fun _ : ι => 𝕜) p) :
    (lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp).coord i x = x i := by
  show (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) p i) x = x i
  rfl

/-- **Basis vectors of the unconditional ℓᵖ basis.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $1 \le p < \infty$ and let $\iota$ be a type. For every $i \in \iota$, the
$i$-th basis vector of the unconditional Schauder basis of $\ell^p(\iota, \mathbb{K})$ by unit
vectors is the unit vector $e_i$, the family equal to $1$ at $i$ and to $0$ elsewhere. -/
@[simp]
theorem lpUnconditionalSchauderBasis_apply [DecidableEq ι] (hp : p ≠ ⊤) (i : ι) :
    (lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp) i
      = lp.single (E := fun _ : ι => 𝕜) p i (1 : 𝕜) := by
  simp [lpUnconditionalSchauderBasis]

/-- **Finite-set projections of the unconditional ℓᵖ basis.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $1 \le p < \infty$ and let $\iota$ be a type. For every finite set
$A \subseteq \iota$ and every $x \in \ell^p(\iota, \mathbb{K})$, the projection $P_A$ of the
unconditional Schauder basis of $\ell^p(\iota, \mathbb{K})$ by unit vectors onto the basis vectors
indexed by $A$ satisfies $P_A x = \sum_{i \in A} x_i e_i$, where $e_i$ is the unit vector equal
to $1$ at $i$ and to $0$ elsewhere. -/
theorem lpUnconditionalSchauderBasis_proj_apply [DecidableEq ι] (hp : p ≠ ⊤)
    (A : Finset ι) (x : lp (fun _ : ι => 𝕜) p) :
    (lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp).proj A x
      = ∑ i ∈ A, lp.single (E := fun _ : ι => 𝕜) p i (x i) := by
  rw [GeneralSchauderBasis.proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lpUnconditionalSchauderBasis_coord_apply, lpUnconditionalSchauderBasis_apply,
    ← lp.single_smul, smul_eq_mul, mul_one]

/-- **Basis projections of $\ell^p$ are contractive.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $\iota$ be an index set and let $1 \le p < \infty$. Let $e_i$ ($i \in \iota$) be
the unit vectors, which form an unconditional Schauder basis of $\ell^p(\iota, \mathbb{K})$. For
every finite set $A \subseteq \iota$ and every $x \in \ell^p(\iota, \mathbb{K})$, the basis
projection $P_A x = \sum_{i \in A} x_i e_i$ satisfies $\|P_A x\|_p \le \|x\|_p$. -/
theorem norm_lpSchauderBasis_proj_apply_le [DecidableEq ι] (hp : p ≠ ⊤)
    (A : Finset ι) (x : lp (fun _ : ι => 𝕜) p) :
    ‖(lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp).proj A x‖ ≤ ‖x‖ := by
  have hp0 : (0 : ℝ) < p.toReal := by
    have h1 : (0 : ℝ≥0∞) < p := zero_lt_one.trans_le Fact.out
    exact ENNReal.toReal_pos h1.ne' hp
  rw [lpUnconditionalSchauderBasis_proj_apply]
  have hnorm : ‖∑ i ∈ A, lp.single p i (x i)‖ ^ p.toReal
      = ∑ i ∈ A, ‖x i‖ ^ p.toReal :=
    lp.norm_sum_single hp0 _ _
  have hsum : ∑ i ∈ A, ‖x i‖ ^ p.toReal ≤ ‖x‖ ^ p.toReal := by
    have hsumm : Summable (fun i => ‖x i‖ ^ p.toReal) :=
      (lp.hasSum_norm hp0 x).summable
    have htsum : ∑' i, ‖x i‖ ^ p.toReal = ‖x‖ ^ p.toReal :=
      (lp.hasSum_norm hp0 x).tsum_eq
    rw [← htsum]
    exact hsumm.sum_le_tsum A (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hle : ‖∑ i ∈ A, lp.single p i (x i)‖ ^ p.toReal ≤ ‖x‖ ^ p.toReal := by
    rw [hnorm]; exact hsum
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp0).mp hle

/-- **The $\ell^p$ basis projections have operator norm at most $1$.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $\iota$ be an index set and let $1 \le p < \infty$. Let $e_i$
($i \in \iota$) be the unit vectors, which form an unconditional Schauder basis of
$\ell^p(\iota, \mathbb{K})$. For every finite set $A \subseteq \iota$, the basis projection
$P_A$, the bounded linear operator on $\ell^p(\iota, \mathbb{K})$ given by
$P_A x = \sum_{i \in A} x_i e_i$, has operator norm $\|P_A\| \le 1$. -/
theorem norm_lpSchauderBasis_proj_le [DecidableEq ι] (hp : p ≠ ⊤) (A : Finset ι) :
    ‖(lpUnconditionalSchauderBasis (ι := ι) (𝕜 := 𝕜) (p := p) hp).proj A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact norm_lpSchauderBasis_proj_apply_le hp A x

/-- **Coordinate functionals of the ℓᵖ Schauder basis.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $1 \le p < \infty$. For every $i \in \mathbb{N}$ and every
$x \in \ell^p(\mathbb{N}, \mathbb{K})$, the $i$-th coordinate functional of the Schauder basis of
$\ell^p(\mathbb{N}, \mathbb{K})$ by unit vectors sends $x$ to its $i$-th entry $x_i$. -/
@[simp]
theorem lpSchauderBasis_coord_apply (hp : p ≠ ⊤)
    (i : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    (lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).coord i x = x i := by
  show (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) p i) x = x i
  rfl

/-- **Basis vectors of the ℓᵖ Schauder basis.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$
and let $1 \le p < \infty$. For every $i \in \mathbb{N}$, the $i$-th basis vector of the Schauder
basis of $\ell^p(\mathbb{N}, \mathbb{K})$ by unit vectors is the unit vector $e_i$, the sequence
equal to $1$ at $i$ and to $0$ elsewhere. -/
@[simp]
theorem lpSchauderBasis_apply (hp : p ≠ ⊤) (i : ℕ) :
    (lpSchauderBasis (𝕜 := 𝕜) (p := p) hp) i
      = lp.single (E := fun _ : ℕ => 𝕜) p i (1 : 𝕜) := by
  simp [lpSchauderBasis]

/-- **The ℓᵖ partial-sum projections are truncations.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $1 \le p < \infty$. For every $n \in \mathbb{N}$ and every
$x \in \ell^p(\mathbb{N}, \mathbb{K})$, the $n$-th partial-sum projection $P_n$ of the Schauder
basis of $\ell^p(\mathbb{N}, \mathbb{K})$ by unit vectors satisfies $P_n x = \sum_{i < n} x_i e_i$,
where $e_i$ is the unit vector equal to $1$ at $i$ and to $0$ elsewhere; that is, $P_n x$ is the
truncation of $x$ to its first $n$ coordinates. -/
theorem lpSchauderBasis_proj_apply (hp : p ≠ ⊤)
    (n : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    (lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).proj n x
      = ∑ i ∈ Finset.range n, lp.single (E := fun _ : ℕ => 𝕜) p i (x i) := by
  rw [SchauderBasis.proj_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lpSchauderBasis_coord_apply, lpSchauderBasis_apply,
    ← lp.single_smul, smul_eq_mul, mul_one]

/-- **The ℓᵖ partial-sum projections are contractions.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $1 \le p < \infty$. For every $n \in \mathbb{N}$ and every
$x \in \ell^p(\mathbb{N}, \mathbb{K})$, the $n$-th partial-sum projection $P_n$ of the Schauder
basis of $\ell^p(\mathbb{N}, \mathbb{K})$ by unit vectors satisfies $\|P_n x\| \le \|x\|$. -/
theorem norm_lpSchauderBasis_classical_proj_apply_le (hp : p ≠ ⊤)
    (n : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    ‖(lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).proj n x‖ ≤ ‖x‖ := by
  have h := norm_lpSchauderBasis_proj_apply_le (ι := ℕ) (𝕜 := 𝕜) (p := p) hp
    (Finset.range n) x
  have heq : (lpUnconditionalSchauderBasis (ι := ℕ) (𝕜 := 𝕜) (p := p) hp).proj
      (Finset.range n) x
      = (lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).proj n x := rfl
  rw [← heq]
  exact h

/-- **The ℓᵖ partial-sum projections have norm at most one.** Let $\mathbb{K}$ be $\mathbb{R}$
or $\mathbb{C}$ and let $1 \le p < \infty$. For every $n \in \mathbb{N}$, the $n$-th partial-sum
projection of the Schauder basis of $\ell^p(\mathbb{N}, \mathbb{K})$ by unit vectors has operator
norm at most $1$. -/
theorem norm_lpSchauderBasis_classical_proj_le (hp : p ≠ ⊤) (n : ℕ) :
    ‖(lpSchauderBasis (𝕜 := 𝕜) (p := p) hp).proj n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact norm_lpSchauderBasis_classical_proj_apply_le hp n x

end MathlibExt.Analysis.Normed.Lp.SchauderBasis
