/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import MathlibExt.Analysis.AbsoluteValue.Rpow

/-!
# Degree-normalized places of a number field

For a number field `K` of degree `d = [K : ℚ]`, this file provides the
degree-normalized finite and infinite absolute values used in height theory.
At a finite place the exponent is `1 / d`, because Mathlib's raw finite absolute value already
incorporates the local degree through the ideal norm. At an infinite place the exponent is
`mult v / d`, where `mult v` is one at a real place and two at a complex place.

The product formula for these normalized values is a separate result and is not asserted here.

## References

* [T. Hilgart and V. Ziegler, *On a conjecture of Levesque and
  Waldschmidt*](https://arxiv.org/abs/2306.11331v1)
* [S. Akhtari, J. D. Vaaler, and M. Widmer, *Small integral generators of totally complex number
  fields*](https://arxiv.org/abs/2307.11849v6)
-/

@[expose] public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Degree-normalized absolute value at a finite place.** Let $K$ be a number field of degree
$d = [K : \mathbb{Q}]$ and let $v$ be a finite place of $K$, with absolute value $|\cdot|_v$. The
degree-normalized absolute value at $v$ is the absolute value $x \mapsto |x|_v^{1/d}$ on $K$.

The finite-place absolute value $|\cdot|_v$ already contains the local-degree factor, so the
remaining normalization exponent is $1/d$. -/
noncomputable def FinitePlace.normalizedAbsoluteValue (v : FinitePlace K) :
    AbsoluteValue K ℝ := by
  refine v.val.rpow (1 / (Module.finrank ℚ K : ℝ)) ?_ ?_
  · have hfinrank : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    positivity
  · have hfinrank : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    rw [div_le_one hfinrank]
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)

/-- **Value of the degree-normalized absolute value at a finite place.** Let $K$ be a number field
of degree $d = [K : \mathbb{Q}]$ and let $v$ be a finite place of $K$, with absolute value
$|\cdot|_v$. For every $x \in K$, the degree-normalized absolute value of $x$ at $v$ equals
$|x|_v^{1/d}$. -/
@[simp]
theorem FinitePlace.normalizedAbsoluteValue_apply (v : FinitePlace K) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  rw [FinitePlace.normalizedAbsoluteValue, AbsoluteValue.rpow_apply, FinitePlace.coe_apply]

/-- **Degree-normalized finite absolute value through the prime ideal.** Let $K$ be a number
field of degree $d = [K : \mathbb{Q}]$, let $v$ be a finite place of $K$, and let $\mathfrak{p}$
be the nonzero prime ideal of the ring of integers of $K$ that defines $v$. For every $x \in K$,
the degree-normalized absolute value of $x$ at $v$ equals $|x|_{\mathfrak{p}}^{1/d}$, where
$|x|_{\mathfrak{p}} = N(\mathfrak{p})^{-v_{\mathfrak{p}}(x)}$ for $x \neq 0$ and
$|0|_{\mathfrak{p}} = 0$, with $N(\mathfrak{p})$ the absolute norm of $\mathfrak{p}$ and
$v_{\mathfrak{p}}$ the $\mathfrak{p}$-adic valuation. -/
theorem FinitePlace.normalizedAbsoluteValue_apply_eq_adicAbv (v : FinitePlace K) (x : K) :
    v.normalizedAbsoluteValue x =
      (HeightOneSpectrum.adicAbv K v.maximalIdeal x) ^
        (1 / (Module.finrank ℚ K : ℝ)) := by
  rw [FinitePlace.normalizedAbsoluteValue_apply,
    ← FinitePlace.norm_embedding v.maximalIdeal x, FinitePlace.norm_embedding_eq]

/-- **Degree-normalized absolute value at an infinite place.** Let $K$ be a number field of degree
$d = [K : \mathbb{Q}]$ and let $v$ be an infinite place of $K$, with absolute value $|\cdot|_v$
and multiplicity $m_v$, equal to $1$ if $v$ is real and $2$ if $v$ is complex. The
degree-normalized absolute value at $v$ is the absolute value $x \mapsto |x|_v^{m_v/d}$ on $K$. -/
noncomputable def InfinitePlace.normalizedAbsoluteValue (v : InfinitePlace K) :
    AbsoluteValue K ℝ := by
  refine v.val.rpow ((v.mult : ℝ) / (Module.finrank ℚ K : ℝ)) ?_ ?_
  · have hmult : 0 < (v.mult : ℝ) := by
      exact_mod_cast InfinitePlace.mult_pos (w := v)
    have hfinrank : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    positivity
  · have hfinrank : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    rw [div_le_one hfinrank]
    exact_mod_cast calc
      v.mult ≤ ∑ w : InfinitePlace K, w.mult :=
        Finset.single_le_sum (fun w _ => Nat.zero_le w.mult) (Finset.mem_univ v)
      _ = Module.finrank ℚ K := InfinitePlace.sum_mult_eq

/-- **Value of the degree-normalized absolute value at an infinite place.** Let $K$ be a number
field of degree $d = [K : \mathbb{Q}]$ and let $v$ be an infinite place of $K$, with absolute
value $|\cdot|_v$ and multiplicity $m_v$, equal to $1$ if $v$ is real and $2$ if $v$ is complex.
For every $x \in K$, the degree-normalized absolute value of $x$ at $v$ equals $|x|_v^{m_v/d}$. -/
@[simp]
theorem InfinitePlace.normalizedAbsoluteValue_apply (v : InfinitePlace K) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ ((v.mult : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  rw [InfinitePlace.normalizedAbsoluteValue, AbsoluteValue.rpow_apply, InfinitePlace.coe_apply]

/-- **Degree-normalized absolute value at a real place.** Let $K$ be a number field of degree
$d = [K : \mathbb{Q}]$ and let $v$ be a real infinite place of $K$, with absolute value
$|\cdot|_v$. For every $x \in K$, the degree-normalized absolute value of $x$ at $v$ equals
$|x|_v^{1/d}$. -/
theorem InfinitePlace.normalizedAbsoluteValue_apply_of_isReal (v : InfinitePlace K)
    (hv : v.IsReal) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  simp [hv.mult_eq_one]

/-- **Degree-normalized absolute value at a complex place.** Let $K$ be a number field of degree
$d = [K : \mathbb{Q}]$ and let $v$ be a complex infinite place of $K$, with absolute value
$|\cdot|_v$. For every $x \in K$, the degree-normalized absolute value of $x$ at $v$ equals
$|x|_v^{2/d}$. -/
theorem InfinitePlace.normalizedAbsoluteValue_apply_of_isComplex (v : InfinitePlace K)
    (hv : v.IsComplex) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ (2 / (Module.finrank ℚ K : ℝ)) := by
  simp [hv.mult_eq_two]

end NumberField
