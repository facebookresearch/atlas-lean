/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Infinite q-Pochhammer products

This file defines the complex infinite q-Pochhammer symbol and proves its
convergence on the open unit disk.

The raw product `qPochhammerInfRaw` is the total `tprod` value, which is `1` by
convention when the factor family is not multipliable. The canonical symbol
`qPochhammerInf` additionally takes convergence evidence `‖q‖ < 1`, so an
out-of-domain `q` cannot be passed silently.

## Main definitions

* `MetaMathlibExt.QPochhammer.qPochhammerInfRaw`
* `MetaMathlibExt.QPochhammer.qPochhammerInf`

## Main statements

* `MetaMathlibExt.QPochhammer.hasProd_qPochhammerInf`
* `MetaMathlibExt.QPochhammer.qPochhammerInfRaw_two_one`
-/

@[expose] public section

namespace MetaMathlibExt.QPochhammer

/-- **Raw infinite q-Pochhammer product.** For complex numbers $a$ and $q$, the raw infinite
q-Pochhammer product is the unconditional infinite product $\prod_{n=0}^{\infty} (1 - a q^n)$,
defined for every $q$: when this product does not converge unconditionally (in particular for
most $q$ with $|q| \ge 1$), its value is $1$ by convention. -/
noncomputable def qPochhammerInfRaw (a q : ℂ) : ℂ :=
  tprod (fun n : ℕ => (1 - a * q ^ n))

/-- **Infinite q-Pochhammer symbol.** For complex numbers $a$ and $q$ with $|q| < 1$, the infinite
q-Pochhammer symbol is $(a;q)_\infty = \prod_{n=0}^{\infty} (1 - a q^n)$, the unconditional
infinite product of the factors $1 - a q^n$.

The hypothesis $|q| < 1$ is an argument of the definition, so the symbol cannot be applied to
$q$ outside the open unit disk.

Source: `2607.10576:D01` / `2608.13818:D02` jointly define
`(a;q)_∞ := ∏_{j=0}^{∞} (1 - a·q^j)` for complex `a, q` with `‖q‖ < 1`. -/
noncomputable def qPochhammerInf (a q : ℂ) (_hq : ‖q‖ < 1) : ℂ :=
  qPochhammerInfRaw a q

/-- **The q-Pochhammer symbol with a = 0.** For every complex number $q$ with $|q| < 1$,
$(0;q)_\infty = 1$, since every factor $1 - 0 \cdot q^n$ equals $1$. -/
@[simp]
theorem qPochhammerInf_zero_left (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInf 0 q hq = 1 := by
  simp [qPochhammerInf, qPochhammerInfRaw]

/-- **Convergence of the infinite q-Pochhammer product.** For all complex numbers $a$ and $q$ with
$|q| < 1$, the infinite product $\prod_{n=0}^{\infty} (1 - a q^n)$ converges unconditionally to
the infinite q-Pochhammer symbol $(a;q)_\infty$: the products of the factors $1 - a q^n$ over
finite sets of indices $n$ tend to $(a;q)_\infty$.

No nonvanishing hypothesis is imposed, so the cases where some factor is zero (and the product
is $0$) are included.

Source: `2607.10576:D01`, where the infinite product $(a;q)_\infty$ is used under $|q| < 1$. -/
theorem hasProd_qPochhammerInf (a q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => (1 - a * q ^ n)) (qPochhammerInf a q hq) := by
  have hs : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_norm_lt_one hq
  have hsa : Summable (fun n : ℕ => (-a) * q ^ n) := hs.mul_left (-a)
  have hm : Multipliable (fun n : ℕ => 1 + (-a) * q ^ n) :=
    Complex.multipliable_one_add_of_summable hsa
  simpa [qPochhammerInf, qPochhammerInfRaw, sub_eq_add_neg] using hm.hasProd

/-- **The q-Pochhammer symbol vanishes at a = 1 and q = 0.** The infinite q-Pochhammer symbol
satisfies $(1;0)_\infty = 0$, because its factor for $n = 0$ is $1 - 1 \cdot 0^0 = 0$ (with the
convention $0^0 = 1$). -/
@[simp]
theorem qPochhammerInf_one_zero : qPochhammerInf 1 0 (by simp) = 0 := by
  have hp := hasProd_qPochhammerInf 1 0 (by simp)
  have hz : HasProd (fun n : ℕ => (1 - (1 : ℂ) * (0 : ℂ) ^ n)) 0 :=
    hasProd_zero_of_exists_eq_zero ⟨0, by simp⟩
  exact hp.unique hz

/-- **The raw q-Pochhammer product at a = 2 and q = 1 equals 1.** The raw infinite q-Pochhammer
product at $a = 2$ and $q = 1$ equals $1$.

Every factor $1 - 2 \cdot 1^n$ equals $-1$, so the finite partial products alternate between $-1$
and $1$ and the product does not converge; the value $1$ is the default that the unconditional
product takes in that case, not a limit of partial products. The q-Pochhammer symbol
$(a;q)_\infty$, which requires $|q| < 1$, excludes such arguments. -/
theorem qPochhammerInfRaw_two_one : qPochhammerInfRaw 2 1 = 1 := by
  have hfactor : ∀ n : ℕ, (1 - (2 : ℂ) * (1 : ℂ) ^ n) = -1 := by
    intro n
    simp only [one_pow, mul_one]
    norm_num
  have hnm : ¬Multipliable (fun n : ℕ => (1 - (2 : ℂ) * (1 : ℂ) ^ n)) := by
    intro hm
    have hm1 : Multipliable (fun _ : ℕ => (-1 : ℂ)) := by
      simpa only [hfactor] using hm
    obtain ⟨m, hmlim⟩ := hm1
    have hlim : Filter.Tendsto (fun n : ℕ => (-1 : ℂ) ^ n) Filter.atTop (nhds m) := by
      have h := hmlim.tendsto_prod_nat
      simpa only [Finset.prod_const, Finset.card_range] using h
    have hshift : Filter.Tendsto (fun n : ℕ => (-1 : ℂ) ^ (n + 1)) Filter.atTop (nhds m) :=
      hlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hnegseq : (fun n : ℕ => (-1 : ℂ) ^ (n + 1)) = fun n : ℕ => -((-1 : ℂ) ^ n) := by
      funext n
      rw [pow_succ]
      ring
    rw [hnegseq] at hshift
    have hmeq : m = -m := tendsto_nhds_unique hshift hlim.neg
    have hm0 : m = 0 := by linear_combination hmeq / 2
    have hmul : Filter.Tendsto (fun n : ℕ => (-1 : ℂ) ^ n * (-1 : ℂ) ^ n) Filter.atTop
        (nhds (m * m)) :=
      hlim.mul hlim
    have hone : (fun n : ℕ => (-1 : ℂ) ^ n * (-1 : ℂ) ^ n) = fun _ : ℕ => (1 : ℂ) := by
      funext n
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n, rfl⟩
    rw [hone] at hmul
    have hsq : m * m = 1 := tendsto_nhds_unique hmul tendsto_const_nhds
    rw [hm0] at hsq
    norm_num at hsq
  change tprod (fun n : ℕ => (1 - (2 : ℂ) * (1 : ℂ) ^ n)) = 1
  exact tprod_eq_one_of_not_multipliable hnm

end MetaMathlibExt.QPochhammer
