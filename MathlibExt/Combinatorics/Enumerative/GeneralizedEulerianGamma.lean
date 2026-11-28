/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Generalized Eulerian polynomials at minus one

The odd coefficients vanish and the signed even coefficients enumerate derangements
with half as many excedances as points and no double excedances.

At this specialization the generating series is the rational power of the hyperbolic secant.
Its successive derivatives enumerate permutations by insertion of a new least element.
Using one color gives the signed excedance sum. Using two colors gives a unique coloring
of each permutation whose cycles alternate between rises and falls.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Number of double excedances.** For a permutation $w$ of $\{0, 1, \dots, n-1\}$, a double
excedance of $w$ is a point $i$ with $w^{-1}(i) < i < w(i)$, and $\mathrm{dexc}(w)$ is the
number of double excedances of $w$.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Section 4. -/
def doubleExcedanceCount {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i ↦ w⁻¹ i < i ∧ i < w i).card

/-- **The identity has no double excedances.** For every $n$, the identity permutation of
$\{0, 1, \dots, n-1\}$ has no double excedances.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Section 4. -/
theorem doubleExcedanceCount_one (n : ℕ) :
    doubleExcedanceCount (1 : Equiv.Perm (Fin n)) = 0 := by
  simp [doubleExcedanceCount]

/-- **Generating function of the generalized Eulerian polynomials.** For rational numbers
$q$, $t$, $x$, $y$ with $x \ne y$, this is the formal power series in $z$ over $\mathbb{Q}$
$$\mathcal{P}(q, t; x, y; z) = \left(\frac{x - y}{x e^{yz} - y e^{xz}}\right)^q e^{(x+y)qtz}.$$
Here the base has constant term $1$, and its $q$-th power is the binomial series
$(1 + u)^q = \sum_{n \ge 0} \binom{q}{n} u^n$ with $u$ the base minus $1$. For $x = y$ the
denominator is zero and the formula above does not apply.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (2). -/
noncomputable def generalizedEulerianSeries (q t x y : ℚ) : PowerSeries ℚ :=
  (binomialSeries ℚ q).subst
      (C (x - y) * (C x * rescale y (exp ℚ) - C y * rescale x (exp ℚ))⁻¹ - 1) *
    rescale ((x + y) * q * t) (exp ℚ)

/-- **Generalized Eulerian polynomials.** For rational numbers $q, t, x, y$ and $n \ge 0$, the
generalized Eulerian polynomial $P_n(q, t; x, y)$ is $n!$ times the coefficient of $z^n$ in the
formal power series over $\mathbb{Q}$
$$\mathcal{P}(q, t; x, y; z) = \left(\frac{x - y}{x e^{yz} - y e^{xz}}\right)^q e^{(x + y) q t z},$$
where the $q$-th power is the binomial series $(1 + u)^q = \sum_{k \ge 0} \binom{q}{k} u^k$
applied to $u = \frac{x - y}{x e^{yz} - y e^{xz}} - 1$. When $x \ne y$ the quotient has constant
term $1$, so $u$ has constant term $0$; for $x = y$ the formula is degenerate and the value of
$P_n$ is a formal convention.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (3). -/
noncomputable def generalizedEulerianP (q t x y : ℚ) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n (generalizedEulerianSeries q t x y)

/-- **Generalized Eulerian polynomials with zero cycle weight.** For all rational numbers
$t, x, y$ and every $n \ge 0$, the generalized Eulerian polynomial satisfies
$P_0(0, t; x, y) = 1$ and $P_n(0, t; x, y) = 0$ for $n \ge 1$.

Indeed, for $q = 0$ the generating function of the polynomials $P_n(0, t; x, y)$ is $1$.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (2). -/
theorem generalizedEulerianP_zero_left (t x y : ℚ) (n : ℕ) :
    generalizedEulerianP 0 t x y n = if n = 0 then 1 else 0 := by
  have hb : binomialSeries ℚ (0 : ℚ) = 1 := by
    simp
  have hs : ∀ u : PowerSeries ℚ, (1 : PowerSeries ℚ).subst u = 1 := by
    intro u
    ext n
    simp [PowerSeries.subst, MvPowerSeries.subst, MvPowerSeries.eval₂]
  unfold generalizedEulerianP generalizedEulerianSeries
  rw [hb, hs, mul_zero, zero_mul, rescale_zero_apply]
  rcases n with _ | n <;> simp [coeff_one]

namespace generalizedEulerianP_neg_one

private abbrev Series := PowerSeries ℚ

-- The denominator is −2 cosh(z), the base is sech(z), and its logarithmic derivative
-- is −tanh(z). In particular the derivative of the slope is its square minus one.
private noncomputable def den : Series := -exp ℚ - rescale (-1) (exp ℚ)

private noncomputable def base : Series := C (-2) * den⁻¹

private noncomputable def slope : Series := -(derivative den) * den⁻¹

private lemma const_negExp : constantCoeff (rescale (-1 : ℚ) (exp ℚ)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp

private lemma const_den : constantCoeff den = -2 := by
  norm_num [den, const_negExp]

private lemma const_base : constantCoeff base = 1 := by
  norm_num [base, constantCoeff_inv, const_den]

private lemma deriv_negExp : derivative (rescale (-1 : ℚ) (exp ℚ)) =
    -rescale (-1 : ℚ) (exp ℚ) := by
  ext n
  have h := congrArg (coeff n) (derivative_exp ℚ)
  rw [coeff_derivative] at h
  simp only [coeff_derivative, coeff_rescale, map_neg, pow_succ]
  linear_combination -(-1 : ℚ) ^ n * h

private lemma deriv_den : derivative den = -exp ℚ + rescale (-1) (exp ℚ) := by
  simp [den, deriv_negExp, derivative_exp]

private lemma const_slope : constantCoeff slope = 0 := by
  simp [slope, deriv_den, const_negExp]

private lemma deriv_slope : derivative slope = slope ^ 2 - 1 := by
  have h : den * den⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by norm_num [const_den])
  have hd : derivative (derivative den) = den := by
    rw [deriv_den, map_add, map_neg, derivative_exp, deriv_negExp, den]
    ring
  simp only [slope, Derivation.leibniz, map_neg, hd, derivative_inv', smul_eq_mul]
  linear_combination -h

private lemma deriv_base : derivative base = base * slope := by
  simp only [base, slope, Derivation.leibniz, derivative_C, derivative_inv', smul_eq_mul]
  ring

private lemma deriv_binomial (q : ℚ) :
    derivative (binomialSeries ℚ q) = C q * binomialSeries ℚ (q - 1) := by
  ext n
  have h := Ring.choose_smul_choose q (n := n + 1) (k := 1) (by omega)
  simpa [coeff_derivative, coeff_C_mul, Ring.choose_one_right, nsmul_eq_mul, mul_comm] using h

private noncomputable def gen (q : ℚ) : Series := (binomialSeries ℚ q).subst (base - 1)

private lemma subst_ok : HasSubst (base - 1) := by
  apply HasSubst.of_constantCoeff_zero'
  simp [const_base]

private lemma const_binomial_subst (q : ℚ) {u : Series} (hu : constantCoeff u = 1) :
    constantCoeff ((binomialSeries ℚ q).subst (u - 1)) = 1 := by
  change MvPowerSeries.constantCoeff _ = _
  rw [constantCoeff_subst_of_constantCoeff_zero]
  · simp
  · change constantCoeff (u - 1) = 0
    simp [hu]

private lemma const_gen (q : ℚ) : constantCoeff (gen q) = 1 :=
  const_binomial_subst q const_base

private lemma deriv_binomial_subst (q : ℚ) {u s : Series} (hu : HasSubst (u - 1))
    (hd : derivative u = u * s) :
    derivative ((binomialSeries ℚ q).subst (u - 1)) =
      C q * s * (binomialSeries ℚ q).subst (u - 1) := by
  have h : binomialSeries ℚ q = binomialSeries ℚ (q - 1) * (1 + X) := by
    convert binomialSeries_add (A := ℚ) (q - 1) 1 using 1
    · rw [sub_add_cancel]
    · rw [← Nat.cast_one (R := ℚ), binomialSeries_nat, pow_one]
  have hs : ((1 + X : Series).subst (u - 1) : Series) = u := by
    rw [← coe_substAlgHom hu, map_add, map_one, substAlgHom_X]
    ring
  rw [derivative_subst hu, deriv_binomial, subst_mul hu, subst_C,
    map_sub, derivative_one, sub_zero, hd]
  conv_rhs => rw [h, subst_mul hu, hs]
  change C q * _ * _ = _
  ring

private lemma deriv_gen (q : ℚ) : derivative (gen q) = C q * slope * gen q :=
  deriv_binomial_subst q subst_ok deriv_base

private lemma coefficient (q t : ℚ) (n : ℕ) :
    generalizedEulerianP q t (-1) 1 n = constantCoeff (derivative^[n] (gen q)) := by
  rw [constantCoeff_iterate_derivative]
  simp [generalizedEulerianP, generalizedEulerianSeries, gen, base, den,
    show (-1 : ℚ) - 1 = -2 by norm_num]

-- Insert the new least element either as a fixed point or in one of the old edges.
-- Colors allow the same product rule to enumerate both families of derangements.
private structure Kernel (α : Type) where
  up : α → α → Series
  flat : α → α → Series
  down : α → α → Series

private def Kernel.edge {α : Type} (K : Kernel α) {n : ℕ} (i j : Fin n) (a b : α) :=
  if i < j then K.up a b else if i = j then K.flat a b else K.down a b

private noncomputable def Kernel.factor {α : Type} (K : Kernel α) {n : ℕ}
    (w : Equiv.Perm (Fin n)) (c : Fin n → α) (i : Fin n) :=
  K.edge i (w i) (c i) (c (w i))

private noncomputable def Kernel.weight {α : Type} (K : Kernel α) (q : ℚ) {n : ℕ}
    (w : Equiv.Perm (Fin n)) (c : Fin n → α) : Series :=
  C (q ^ cycleQuotientCount w) * ∏ i, K.factor w c i

private lemma fixed_insert {α : Type} (K : Kernel α) (q : ℚ) {n : ℕ}
    (w : Equiv.Perm (Fin n)) (c : Fin n → α) (b : α) :
    K.weight q (Equiv.Perm.decomposeFin.symm (0, w)) (Fin.cons b c) =
      C q * K.flat b b * K.weight q w c := by
  simp [Kernel.weight, cycleQuotientCount_decomposeFin_zero, pow_succ, Fin.prod_univ_succ,
    Kernel.factor, Kernel.edge]
  ring

private lemma split_insert {α : Type} (K : Kernel α) (q : ℚ) {n : ℕ}
    (w : Equiv.Perm (Fin n)) (c : Fin n → α) (b : α) (i : Fin n) :
    K.weight q (Equiv.Perm.decomposeFin.symm ((w i).succ, w)) (Fin.cons b c) =
      C (q ^ cycleQuotientCount w) * (K.down (c i) b * K.up b (c (w i))) *
        ∏ j ∈ Finset.univ.erase i, K.factor w c j := by
  unfold Kernel.weight
  rw [cycleQuotientCount_decomposeFin_succ, Fin.prod_univ_succ,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have he (j : Fin n) (hj : j ≠ i) : (Equiv.Perm.decomposeFin.symm ((w i).succ, w)) j.succ =
      (w j).succ := by
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_of_ne_of_ne]
    · exact Fin.succ_ne_zero _
    · exact fun h => hj (w.injective (Fin.succ_injective _ h))
  have hp : (∏ j ∈ Finset.univ.erase i,
      K.factor (Equiv.Perm.decomposeFin.symm ((w i).succ, w)) (Fin.cons b c) j.succ) =
      ∏ j ∈ Finset.univ.erase i, K.factor w c j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    simp [Kernel.factor, he j (Finset.ne_of_mem_erase hj), Kernel.edge]
  rw [hp]
  simp [Kernel.factor, Kernel.edge]
  ring

private lemma deriv_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → Series) :
    derivative (∏ i ∈ s, f i) = ∑ i ∈ s, derivative (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, Finset.sum_insert ha, ih,
      Finset.erase_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.erase_insert_of_ne (show a ≠ i from fun h => ha (h.symm ▸ hi)),
        Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring

-- Splitting an edge replaces it by a fall followed by a rise. Summing over the
-- color of the new vertex gives the derivative of the original edge weight.
private lemma insert_sum {α : Type} [Fintype α] (K : Kernel α)
    (hd : ∀ {m : ℕ} (i j : Fin m) a b,
      derivative (K.edge i j a b) = ∑ v, K.down a v * K.up v b)
    (q : ℚ) {n : ℕ} (w : Equiv.Perm (Fin n)) (c : Fin n → α) :
    ∑ p : Fin (n + 1), ∑ b : α,
        K.weight q (Equiv.Perm.decomposeFin.symm (p, w)) (Fin.cons b c) =
      C q * (∑ b, K.flat b b) * K.weight q w c + derivative (K.weight q w c) := by
  rw [Fin.sum_univ_succ]
  congr 1
  · simp_rw [fixed_insert]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  · rw [← Equiv.sum_comp w (fun j => ∑ b : α,
      K.weight q (Equiv.Perm.decomposeFin.symm (j.succ, w)) (Fin.cons b c))]
    simp_rw [split_insert]
    simp only [Kernel.weight, Derivation.leibniz, derivative_C, smul_eq_mul, mul_zero,
      add_zero, deriv_prod, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show derivative (K.factor w c i) = _ from hd i (w i) _ _, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

private lemma expand_derivatives {α : Type} [Fintype α] (K : Kernel α) (q : ℚ) (g : Series)
    (hg : derivative g = C q * (∑ b, K.flat b b) * g)
    (hd : ∀ {m : ℕ} (i j : Fin m) a b,
      derivative (K.edge i j a b) = ∑ v, K.down a v * K.up v b) (n : ℕ) :
    derivative^[n] g = g * ∑ w : Equiv.Perm (Fin n), ∑ c, K.weight q w c := by
  classical
  induction n with
  | zero =>
    have hc : cycleQuotientCount (1 : Equiv.Perm (Fin 0)) = 0 := by
      simp [cycleQuotientCount_eq]
    simp [Kernel.weight, Finset.univ_unique, hc, Subsingleton.elim (default : Equiv.Perm (Fin 0)) 1]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, hg]
    simp only [smul_eq_mul, map_sum]
    have splitColors (v : Equiv.Perm (Fin (n + 1))) :
        ∑ c, K.weight q v c = ∑ c : Fin n → α, ∑ b : α, K.weight q v (Fin.cons b c) := by
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp (K.weight q v),
        Fintype.sum_prod_type_right]
      rfl
    conv_rhs =>
      rw [← Equiv.Perm.decomposeFin.symm.sum_comp
        (fun w : Equiv.Perm (Fin (n + 1)) => ∑ c, K.weight q w c), Fintype.sum_prod_type_right]
    simp_rw [splitColors]
    have hs (w : Equiv.Perm (Fin n)) :
        ∑ p : Fin (n + 1), ∑ c : Fin n → α, ∑ b : α,
            K.weight q (Equiv.Perm.decomposeFin.symm (p, w)) (Fin.cons b c) =
          ∑ c, (C q * (∑ b, K.flat b b) * K.weight q w c + derivative (K.weight q w c)) := by
      rw [Finset.sum_comm]
      simp_rw [insert_sum K hd]
    simp_rw [hs, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

private lemma expand {α : Type} [Fintype α] (K : Kernel α)
    (hfix : ∑ b, K.flat b b = slope)
    (hd : ∀ {m : ℕ} (i j : Fin m) a b,
      derivative (K.edge i j a b) = ∑ v, K.down a v * K.up v b)
    (q : ℚ) (n : ℕ) :
    derivative^[n] (gen q) = gen q * ∑ w : Equiv.Perm (Fin n), ∑ c, K.weight q w c :=
  expand_derivatives K q (gen q) (by rw [hfix, deriv_gen]) hd n

private noncomputable def signedKernel : Kernel Unit where
  up _ _ := slope - 1
  flat _ _ := slope
  down _ _ := slope + 1

-- At zero the only surviving edges go up from false to true or down from true to false.
private noncomputable def alternatingKernel : Kernel Bool where
  up a b := if b then (if a then slope else -1) else 0
  flat a b := if a && b then slope else 0
  down a b := if a then (if b then slope else 1) else 0

private lemma signed_expand (q t : ℚ) (m : ℕ) :
    generalizedEulerianP q t (-1) 1 m =
      ∑ w : Equiv.Perm (Fin m), constantCoeff (signedKernel.weight q w fun _ => ()) := by
  rw [coefficient, expand signedKernel, map_mul, const_gen, one_mul, map_sum]
  · simp
  · simp [signedKernel]
  · intro m i j a b
    simp only [Kernel.edge]
    split_ifs <;> simp [signedKernel, deriv_slope] <;> ring

private lemma alternating_expand (q t : ℚ) (m : ℕ) :
    generalizedEulerianP q t (-1) 1 m =
      ∑ w : Equiv.Perm (Fin m), ∑ c, constantCoeff (alternatingKernel.weight q w c) := by
  rw [coefficient, expand alternatingKernel, map_mul, const_gen, one_mul, map_sum]
  · simp only [map_sum]
  · simp [alternatingKernel]
  · intro m i j a b
    simp only [Kernel.edge]
    split_ifs <;> cases a <;> cases b <;> simp [alternatingKernel, deriv_slope] <;> ring

private lemma noFixed {m : ℕ} (w : Equiv.Perm (Fin m)) :
    Fintype.card (Function.fixedPoints w) = 0 ↔ ∀ i, i ≠ w i := by
  rw [Fintype.card_eq_zero_iff, isEmpty_subtype]
  exact forall_congr' fun i => not_congr eq_comm

private lemma signed_weight (q : ℚ) {m : ℕ} (w : Equiv.Perm (Fin m)) :
    constantCoeff (signedKernel.weight q w fun _ => ()) =
      if Fintype.card (Function.fixedPoints w) = 0 then
        q ^ cycleQuotientCount w * (-1) ^ excedanceCount m w else 0 := by
  rw [Kernel.weight, map_mul, constantCoeff_C, map_prod]
  split_ifs with hw
  · have h := (noFixed w).mp hw
    simp [Kernel.factor, Kernel.edge, signedKernel, apply_ite constantCoeff, const_slope, h,
      Finset.prod_ite, excedanceCount]
  · obtain ⟨i, hi⟩ := not_forall.mp (mt (noFixed w).mpr hw)
    have he : i = w i := not_not.mp hi
    have hz : constantCoeff (signedKernel.factor w (fun _ => ()) i) = 0 := by
      simp [Kernel.factor, Kernel.edge, ← he, signedKernel, const_slope]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]

private def Alternates {m : ℕ} (w : Equiv.Perm (Fin m)) : Prop :=
  ∀ i, i < w i ↔ ¬ w i < w (w i)

-- The excedance set and its image are disjoint exactly when there are no double
-- excedances. They partition all the vertices exactly when the cycles alternate.
private lemma alternate_iff {m : ℕ} (w : Equiv.Perm (Fin m)) :
    Alternates w ↔ 2 * excedanceCount m w = m ∧ doubleExcedanceCount w = 0 := by
  let u := Finset.univ.filter fun i => i < w i
  have hu : u.card = excedanceCount m w := rfl
  have him : (u.image w).card = u.card := Finset.card_image_of_injective _ w.injective
  have hco : uᶜ.card = m - u.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hle : u.card ≤ m := by simpa using u.card_le_univ
  have mem (i : Fin m) : w i ∈ u.image w ↔ i < w i := by simp [u, w.injective.eq_iff]
  have hdouble : doubleExcedanceCount w = 0 ↔ ∀ i, i < w i → ¬w i < w (w i) := by
    simp only [doubleExcedanceCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_and]
    constructor
    · intro h i
      simpa using @h (w i)
    · intro h i
      simpa using h (w⁻¹ i)
  rw [← hu, hdouble]
  constructor
  · intro h
    have sets : u.image w = uᶜ := by
      ext j
      obtain ⟨i, rfl⟩ := w.surjective j
      rw [mem, Finset.mem_compl, Finset.mem_filter]
      simpa using h i
    rw [sets, hco] at him
    exact ⟨by omega, fun i => (h i).mp⟩
  · rintro ⟨hcard, h⟩
    have sub : u.image w ⊆ uᶜ := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      simpa [u] using h i (Finset.mem_filter.mp hi).2
    have sets : u.image w = uᶜ := Finset.eq_of_subset_of_card_le sub (by omega)
    intro i
    rw [← mem, sets]
    simp [u]

private lemma alternate_noFixed {m : ℕ} {w : Equiv.Perm (Fin m)} (h : Alternates w) :
    Fintype.card (Function.fixedPoints w) = 0 := by
  apply (noFixed w).mpr
  intro i hi
  simpa [← hi] using h i

private def Valid {m : ℕ} (w : Equiv.Perm (Fin m)) (c : Fin m → Bool) (i : Fin m) : Prop :=
  i ≠ w i ∧ c i = decide (¬ i < w i) ∧ c (w i) = decide (i < w i)

private lemma valid_iff {m : ℕ} (w : Equiv.Perm (Fin m)) (c : Fin m → Bool) :
    (∀ i, Valid w c i) ↔ Alternates w ∧ c = (fun i => decide (¬ i < w i)) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, funext fun i => (h i).2.1⟩
    have he := (h i).2.2.symm.trans (h (w i)).2.1
    simpa only [decide_eq_decide] using he
  · rintro ⟨h, rfl⟩ i
    refine ⟨(noFixed w).mp (alternate_noFixed h) i, rfl, ?_⟩
    simp only [decide_eq_decide]
    exact (h i).symm

private lemma alternating_weight (q : ℚ) {m : ℕ} (w : Equiv.Perm (Fin m)) :
    ∑ c, constantCoeff (alternatingKernel.weight q w c) =
      if 2 * excedanceCount m w = m ∧ doubleExcedanceCount w = 0 then
        q ^ cycleQuotientCount w * (-1) ^ excedanceCount m w else 0 := by
  classical
  let v := fun i : Fin m => decide (¬ i < w i)
  have localWeight (c : Fin m → Bool) (i : Fin m) :
      constantCoeff (alternatingKernel.factor w c i) =
        if Valid w c i then (if i < w i then -1 else 1) else 0 := by
    rcases lt_trichotomy i (w i) with hi | hi | hi
    · cases h₁ : c i <;> cases h₂ : c (w i) <;>
        simp [Kernel.factor, Kernel.edge, alternatingKernel, Valid, hi, hi.ne, h₁, h₂, const_slope]
    · simp [Kernel.factor, Kernel.edge, ← hi, Valid, alternatingKernel, apply_ite constantCoeff,
        const_slope]
    · cases h₁ : c i <;> cases h₂ : c (w i) <;>
        simp [Kernel.factor, Kernel.edge, alternatingKernel, Valid, hi.not_gt, hi.ne', h₁, h₂,
          const_slope]
  have weight (c : Fin m → Bool) :
      constantCoeff (alternatingKernel.weight q w c) =
        if Alternates w ∧ c = v then q ^ cycleQuotientCount w * (-1) ^ excedanceCount m w
        else 0 := by
    rw [Kernel.weight, map_mul, constantCoeff_C, map_prod]
    split_ifs with h
    · have hv := (valid_iff w c).mpr h
      simp [localWeight, hv, Finset.prod_ite, excedanceCount]
    · obtain ⟨i, hi⟩ := not_forall.mp (mt (valid_iff w c).mp h)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [localWeight, ite_eq_right hi]), mul_zero]
  simp_rw [weight]
  by_cases h : Alternates w
  · simp [h, (alternate_iff w).mp h]
  · simp only [h, false_and, ite_false, Finset.sum_const_zero,
      ite_eq_right (mt (alternate_iff w).mpr h)]

end generalizedEulerianP_neg_one

open generalizedEulerianP_neg_one

/-- **Generalized Eulerian polynomials at $x = -1$, $y = 1$.** Let $P_m(q, t; x, y)$ be the
generalized Eulerian polynomial. For a permutation $w$ write $\mathrm{cyc}(w)$ for its number of
cycles (fixed points counted as cycles), $\mathrm{exc}(w)$ for its number of excedances (points
$i$ with $w(i) > i$) and $\mathrm{dexc}(w)$ for its number of double excedances, and let $D_{2n}$
be the set of derangements (permutations without fixed points) of $\{0, 1, \dots, 2n-1\}$. Then
for all rational numbers $q, t$ and every $n \ge 0$, $P_{2n+1}(q, t; -1, 1) = 0$ and
$$
(-1)^n P_{2n}(q, t; -1, 1) = \sum_{w \in D_{2n}} q^{\mathrm{cyc}(w)} (-1)^{n - \mathrm{exc}(w)}
= \sum_{w \in D_{2n},\ \mathrm{exc}(w) = n,\ \mathrm{dexc}(w) = 0} q^{\mathrm{cyc}(w)},
$$
where the exponent $n - \mathrm{exc}(w)$ is an integer, possibly negative.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Corollary 8
(`jis-2024-24.1.5-cor-8`). -/
theorem generalizedEulerianP_neg_one (q t : ℚ) (n : ℕ) :
    generalizedEulerianP q t (-1) 1 (2 * n + 1) = 0 ∧
      (-1) ^ n * generalizedEulerianP q t (-1) 1 (2 * n) =
        ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
            Fintype.card (Function.fixedPoints w) = 0),
          q ^ cycleQuotientCount w * (-1 : ℚ) ^ ((n : ℤ) - excedanceCount (2 * n) w) ∧
      ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
          Fintype.card (Function.fixedPoints w) = 0),
          q ^ cycleQuotientCount w * (-1 : ℚ) ^ ((n : ℤ) - excedanceCount (2 * n) w) =
        ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
            Fintype.card (Function.fixedPoints w) = 0 ∧ excedanceCount (2 * n) w = n ∧
              doubleExcedanceCount w = 0), q ^ cycleQuotientCount w := by
  classical
  have odd (w : Equiv.Perm (Fin (2 * n + 1))) :
      ¬ 2 * excedanceCount (2 * n + 1) w = 2 * n + 1 := by omega
  constructor
  · rw [alternating_expand]
    simp [alternating_weight, odd]
  have signed := signed_expand q t (2 * n)
  simp_rw [signed_weight] at signed
  have sign (e : ℕ) : (-1 : ℚ) ^ ((n : ℤ) - e) = (-1) ^ n * (-1) ^ e := by
    rw [zpow_sub₀ (by norm_num : (-1 : ℚ) ≠ 0), zpow_natCast, zpow_natCast,
      div_eq_mul_inv, ← inv_pow, inv_neg_one]
  have hs : (-1) ^ n * generalizedEulerianP q t (-1) 1 (2 * n) =
      ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
        Fintype.card (Function.fixedPoints w) = 0),
        q ^ cycleQuotientCount w * (-1 : ℚ) ^ ((n : ℤ) - excedanceCount (2 * n) w) := by
    rw [signed, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> simp [sign]
    ring
  refine ⟨hs, hs.symm.trans ?_⟩
  rw [alternating_expand, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [alternating_weight]
  by_cases h : 2 * excedanceCount (2 * n) w = 2 * n ∧ doubleExcedanceCount w = 0
  · have he : excedanceCount (2 * n) w = n := by omega
    have hf := alternate_noFixed ((alternate_iff w).mpr h)
    simp only [he, hf, h.2, and_self, ite_true]
    rw [mul_left_comm, ← mul_pow]
    norm_num
  · have h' : ¬(Fintype.card (Function.fixedPoints w) = 0 ∧
        excedanceCount (2 * n) w = n ∧ doubleExcedanceCount w = 0) := by
      rintro ⟨_, he, hd⟩
      exact h ⟨by rw [he], hd⟩
    simp only [ite_eq_right h, ite_eq_right h', mul_zero]

namespace generalizedEulerianP_eq_sum_perm

open generalizedEulerianP_neg_one

private noncomputable def expAt (a : ℚ) : Series := rescale a (exp ℚ)

private lemma const_expAt (a : ℚ) : constantCoeff (expAt a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, expAt, coeff_rescale]
  simp

private lemma deriv_expAt (a : ℚ) : derivative (expAt a) = C a * expAt a := by
  ext n
  have h := congrArg (coeff n) (derivative_exp ℚ)
  rw [coeff_derivative] at h
  simp only [expAt, coeff_derivative, coeff_rescale, coeff_C_mul, pow_succ]
  linear_combination a ^ n * a * h

private noncomputable def den (x y : ℚ) : Series := C x * expAt y - C y * expAt x

private noncomputable def base (x y : ℚ) : Series := C (x - y) * (den x y)⁻¹

private noncomputable def slope (x y : ℚ) : Series := -derivative (den x y) * (den x y)⁻¹

private lemma const_den (x y : ℚ) : constantCoeff (den x y) = x - y := by
  simp [den, const_expAt]

private lemma const_base {x y : ℚ} (hxy : x ≠ y) : constantCoeff (base x y) = 1 := by
  simp [base, constantCoeff_inv, const_den, sub_ne_zero.mpr hxy]

private lemma deriv_den (x y : ℚ) : derivative (den x y) = C (x * y) * (expAt y - expAt x) := by
  simp only [den, map_sub, Derivation.leibniz, derivative_C, smul_eq_mul,
    deriv_expAt, map_mul]
  ring

private lemma const_slope (x y : ℚ) : constantCoeff (slope x y) = 0 := by
  simp [slope, deriv_den, const_expAt]

-- Differentiating −den′/den uses the second-order equation for the two exponentials.
private lemma deriv_slope {x y : ℚ} (hxy : x ≠ y) :
    derivative (slope x y) = (slope x y + C y) * (slope x y + C x) := by
  have hd : derivative (derivative (den x y)) =
      C (x + y) * derivative (den x y) - C (x * y) * den x y := by
    rw [deriv_den, den]
    simp only [map_sub, Derivation.leibniz, derivative_C, smul_eq_mul, deriv_expAt,
      map_add, map_mul]
    ring
  have hu := PowerSeries.mul_inv_cancel (den x y) (by rw [const_den]; exact sub_ne_zero.mpr hxy)
  simp only [slope, Derivation.leibniz, map_neg, derivative_inv', hd, smul_eq_mul, map_add, map_mul]
  linear_combination C x * C y * hu

private lemma deriv_base (x y : ℚ) : derivative (base x y) = base x y * slope x y := by
  simp only [base, slope, Derivation.leibniz, derivative_C, derivative_inv', smul_eq_mul]
  ring

private lemma const_series (q t : ℚ) {x y : ℚ} (hxy : x ≠ y) :
    constantCoeff (generalizedEulerianSeries q t x y) = 1 := by
  change constantCoeff ((binomialSeries ℚ q).subst (base x y - 1) * expAt ((x + y) * q * t)) = 1
  rw [map_mul, const_expAt, mul_one]
  exact const_binomial_subst q (const_base hxy)

private lemma deriv_series (q t : ℚ) {x y : ℚ} (hxy : x ≠ y) :
    derivative (generalizedEulerianSeries q t x y) =
      C q * (slope x y + C ((x + y) * t)) * generalizedEulerianSeries q t x y := by
  have hs : HasSubst (base x y - 1) := HasSubst.of_constantCoeff_zero' (by simp [const_base hxy])
  have hb := deriv_binomial_subst q hs (deriv_base x y)
  change derivative ((binomialSeries ℚ q).subst (base x y - 1) * expAt ((x + y) * q * t)) =
    _ * _ * ((binomialSeries ℚ q).subst (base x y - 1) * expAt ((x + y) * q * t))
  simp only [Derivation.leibniz, smul_eq_mul, hb, deriv_expAt, map_mul]
  ring

-- Splitting an edge inserts a fall and a rise. At z = 0 the slope vanishes, leaving
-- the weights x, (x + y)t and y for a rise, a fixed point and a fall, respectively.
private noncomputable def kernel (t x y : ℚ) : Kernel Unit where
  up _ _ := slope x y + C x
  flat _ _ := slope x y + C ((x + y) * t)
  down _ _ := slope x y + C y

private lemma card_falls {n : ℕ} (w : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun i ↦ w i < i).card = excedanceCount n w⁻¹ := by
  rw [excedanceCount, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (w.subtypeEquiv fun i ↦ by simp)

private lemma const_weight (q t x y : ℚ) {n : ℕ} (w : Equiv.Perm (Fin n)) :
    constantCoeff ((kernel t x y).weight q w fun _ ↦ ()) =
      q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w) *
        x ^ excedanceCount n w * y ^ excedanceCount n w⁻¹ *
        (x + y) ^ Fintype.card (Function.fixedPoints w) := by
  rw [Kernel.weight, map_mul, constantCoeff_C, map_prod]
  have h (i : Fin n) : constantCoeff ((kernel t x y).factor w (fun _ ↦ ()) i) =
      (if i < w i then x else 1) * (if w i < i then y else 1) *
        (if w i = i then (x + y) * t else 1) := by
    rcases lt_trichotomy i (w i) with hi | hi | hi
    · simp [Kernel.factor, Kernel.edge, kernel, hi, hi.ne', hi.not_gt, const_slope]
    · simp [Kernel.factor, Kernel.edge, kernel, ← hi, const_slope]
    · simp [Kernel.factor, Kernel.edge, kernel, hi, hi.ne, hi.ne', hi.not_gt, const_slope]
  have hfix : (Finset.univ.filter fun i ↦ w i = i).card = Fintype.card (Function.fixedPoints w) :=
    (Fintype.card_subtype fun i ↦ w i = i).symm
  simp_rw [h, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]
  rw [card_falls, hfix, mul_pow]
  change q ^ _ * (x ^ excedanceCount n w * y ^ _ * _) = _
  ring

private lemma coefficient (q t : ℚ) {x y : ℚ} (hxy : x ≠ y) (n : ℕ) :
    generalizedEulerianP q t x y n =
      ∑ w : Equiv.Perm (Fin n), constantCoeff ((kernel t x y).weight q w fun _ ↦ ()) := by
  rw [generalizedEulerianP, ← constantCoeff_iterate_derivative,
    expand_derivatives (kernel t x y) q (generalizedEulerianSeries q t x y)]
  · simp [const_series q t hxy, map_sum]
  · simpa [kernel] using deriv_series q t hxy
  · intro m i j a b
    simp only [Kernel.edge]
    split_ifs <;> simp [kernel, deriv_slope hxy]

end generalizedEulerianP_eq_sum_perm

/-- **Permutation expansion of the generalized Eulerian polynomials.** Let $P_n(q, t; x, y)$ be
the generalized Eulerian polynomial and let $S_n$ be the set of permutations of
$\{0, 1, \dots, n-1\}$. For $w \in S_n$ write $\mathrm{cyc}(w)$ for the number of cycles of $w$
(fixed points counted as cycles), $\mathrm{fix}(w)$ for the number of fixed points of $w$, and
$\mathrm{exc}(w)$ for the number of excedances of $w$, the points $i$ with $w(i) > i$. Then for
all rational numbers $q, t, x, y$ with $x \ne y$ and every $n \ge 0$,
$$
P_n(q, t; x, y) = \sum_{w \in S_n} q^{\mathrm{cyc}(w)} t^{\mathrm{fix}(w)} x^{\mathrm{exc}(w)}
y^{\mathrm{exc}(w^{-1})} (x + y)^{\mathrm{fix}(w)}.
$$

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 2
(`jis-2024-24.1.5-thm-2`). -/
public theorem generalizedEulerianP_eq_sum_perm (q t x y : ℚ) (hxy : x ≠ y) (n : ℕ) :
    generalizedEulerianP q t x y n =
      ∑ w : Equiv.Perm (Fin n),
        q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w) *
          x ^ excedanceCount n w * y ^ excedanceCount n w⁻¹ *
          (x + y) ^ Fintype.card (Function.fixedPoints w) := by
  rw [generalizedEulerianP_eq_sum_perm.coefficient q t hxy n]
  exact Finset.sum_congr rfl fun w _ ↦ generalizedEulerianP_eq_sum_perm.const_weight q t x y w

namespace generalizedEulerianP_gamma_nonneg

open generalizedEulerianP_eq_sum_perm

-- A summand records powers of q, t, x + y, xy and the logarithmic slope, in that order.
-- Its multiplicity is independent of all four parameters.
private structure Term where
  count : ℕ
  qDeg : ℕ
  tDeg : ℕ
  linearDeg : ℕ
  quadDeg : ℕ
  slopeDeg : ℕ

private noncomputable def Term.eval (m : Term) (q t x y : ℚ) : Series :=
  C ((m.count : ℚ) * q ^ m.qDeg * t ^ m.tDeg * (x + y) ^ m.linearDeg * (x * y) ^ m.quadDeg) *
    slope x y ^ m.slopeDeg

-- The first two branches differentiate the generating series. The remaining three
-- differentiate the slope power using s' = s² + (x + y)s + xy.
private def Term.step (m : Term) (a : Fin 5) : Term :=
  if a = 0 then { m with qDeg := m.qDeg + 1, slopeDeg := m.slopeDeg + 1 }
  else if a = 1 then { m with qDeg := m.qDeg + 1, tDeg := m.tDeg + 1, linearDeg := m.linearDeg + 1 }
  else if a = 2 then { m with count := m.count * m.slopeDeg, slopeDeg := m.slopeDeg + 1 }
  else if a = 3 then { m with count := m.count * m.slopeDeg, linearDeg := m.linearDeg + 1 }
  else
    { m with
      count := m.count * m.slopeDeg
      quadDeg := m.quadDeg + 1
      slopeDeg := m.slopeDeg - 1 }

private lemma deriv_slope_pow {x y : ℚ} (hxy : x ≠ y) (l : ℕ) :
    derivative (slope x y ^ l) = (l : Series) *
      (slope x y ^ (l + 1) + C (x + y) * slope x y ^ l + C (x * y) * slope x y ^ (l - 1)) := by
  cases l with
  | zero => simp
  | succ l =>
    rw [derivative_pow, deriv_slope hxy]
    simp only [Nat.succ_sub_one, map_add, map_mul, pow_succ]
    ring

private lemma Term.derivative_eval (m : Term) (q t : ℚ) {x y : ℚ} (hxy : x ≠ y) :
    derivative (m.eval q t x y * generalizedEulerianSeries q t x y) =
      ∑ a : Fin 5, (m.step a).eval q t x y * generalizedEulerianSeries q t x y := by
  rw [Derivation.leibniz, Term.eval, Derivation.leibniz, derivative_C, deriv_slope_pow hxy,
    deriv_series q t hxy]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num [Term.step, Term.eval, smul_eq_mul, pow_succ, map_mul]
  ring

-- Both parameter degrees grow by at most one per step. A nonzero term gains one unit
-- of weight: in the last branch one slope factor is replaced by the weight-two factor xy.
private def Term.Valid (n : ℕ) (m : Term) : Prop :=
  m.count ≠ 0 → m.qDeg ≤ n ∧ m.tDeg ≤ n ∧ m.linearDeg + 2 * m.quadDeg + m.slopeDeg = n

private lemma Term.valid_step {n : ℕ} {m : Term} (hm : m.Valid n) (a : Fin 5) :
    (m.step a).Valid (n + 1) := by
  fin_cases a <;> norm_num [Term.Valid, Term.step, mul_ne_zero_iff] at *
  all_goals
    intro h
    obtain ⟨hi, hj, hd⟩ := hm h
    omega

-- A history chooses one summand of the product rule at each differentiation.
private def term : (n : ℕ) → (Fin n → Fin 5) → Term
  | 0, _ => ⟨1, 0, 0, 0, 0, 0⟩
  | n + 1, a => (term n fun i ↦ a i.succ).step (a 0)

private lemma term_valid (n : ℕ) (a : Fin n → Fin 5) : (term n a).Valid n := by
  induction n with
  | zero => simp [term, Term.Valid]
  | succ n ih => exact Term.valid_step (ih fun i ↦ a i.succ) (a 0)

private lemma iterate_eq (q t : ℚ) {x y : ℚ} (hxy : x ≠ y) (n : ℕ) :
    derivative^[n] (generalizedEulerianSeries q t x y) =
      ∑ a : Fin n → Fin 5, (term n a).eval q t x y * generalizedEulerianSeries q t x y := by
  classical
  induction n with
  | zero => simp [Finset.univ_unique, term, Term.eval]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    simp_rw [Term.derivative_eval _ q t hxy]
    conv_rhs =>
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Fin 5)).sum_comp
        (fun a ↦ (term (n + 1) a).eval q t x y * generalizedEulerianSeries q t x y),
        Fintype.sum_prod_type_right]
    simp [term]

private def survivors (n : ℕ) : Finset (Fin n → Fin 5) :=
  Finset.univ.filter fun a ↦ (term n a).count ≠ 0 ∧ (term n a).slopeDeg = 0

private def Term.key (m : Term) : ℕ × ℕ × ℕ := (m.quadDeg, m.qDeg, m.tDeg)

private lemma coefficient_eq (q t : ℚ) {x y : ℚ} (hxy : x ≠ y) (n : ℕ) :
    generalizedEulerianP q t x y n =
      ∑ a ∈ survivors n,
        ((term n a).count : ℚ) * q ^ (term n a).qDeg * t ^ (term n a).tDeg *
          (x * y) ^ (term n a).quadDeg * (x + y) ^ (n - 2 * (term n a).quadDeg) := by
  rw [generalizedEulerianP, ← constantCoeff_iterate_derivative, iterate_eq q t hxy]
  simp only [map_sum, map_mul, const_series q t hxy, mul_one, survivors, Finset.sum_filter,
    Term.eval, constantCoeff_C, map_pow, generalizedEulerianP_eq_sum_perm.const_slope]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases hc : (term n a).count = 0
  · simp [hc]
  by_cases hs : (term n a).slopeDeg = 0
  · have hd := ((term_valid n a) hc).2.2
    have hb : (term n a).linearDeg = n - 2 * (term n a).quadDeg := by omega
    simp [hc, hs, hb]
    ring
  · simp [hs, zero_pow]

private def gammaCoeff (n k i j : ℕ) : ℕ :=
  ∑ a ∈ (survivors n).filter (fun a ↦ (term n a).key = (k, i, j)), (term n a).count

private lemma grouped (q t : ℚ) {x y : ℚ} (hxy : x ≠ y) (n : ℕ) :
    generalizedEulerianP q t x y n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (gammaCoeff n k i j : ℚ) * q ^ i * t ^ j) * x ^ k * y ^ k * (x + y) ^ (n - 2 * k) := by
  let indices : Finset (ℕ × ℕ × ℕ) :=
    Finset.range (n / 2 + 1) ×ˢ (Finset.range (n + 1) ×ˢ Finset.range (n + 1))
  let weight : ℕ × ℕ × ℕ → ℚ := fun (k, i, j) ↦
    q ^ i * t ^ j * (x * y) ^ k * (x + y) ^ (n - 2 * k)
  have hm : ∀ a ∈ survivors n, (term n a).key ∈ indices := by
    intro a ha
    obtain ⟨hc, hs⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨hi, hj, hd⟩ := (term_valid n a) hc
    simp only [indices, Term.key, Finset.mem_product, Finset.mem_range]
    omega
  calc
    _ = ∑ a ∈ survivors n, ((term n a).count : ℚ) * weight (term n a).key := by
      rw [coefficient_eq q t hxy]
      exact Finset.sum_congr rfl fun a _ ↦ by simp only [Term.key, weight]; ring
    _ = ∑ b ∈ indices, ∑ a ∈ (survivors n).filter (fun a ↦ (term n a).key = b),
          ((term n a).count : ℚ) * weight (term n a).key :=
      (Finset.sum_fiberwise_of_maps_to hm _).symm
    _ = ∑ b ∈ indices,
          ((∑ a ∈ (survivors n).filter (fun a ↦ (term n a).key = b), (term n a).count : ℕ) : ℚ) *
            weight b := by
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [Nat.cast_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a ha ↦ by rw [(Finset.mem_filter.mp ha).2]
    _ = _ := by
      simp only [indices, Finset.sum_product, weight, mul_pow, Finset.sum_mul, gammaCoeff]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      ring

end generalizedEulerianP_gamma_nonneg

/-- **The gamma coefficients of the generalized Eulerian polynomials have nonnegative integer
coefficients.** Fix $n \ge 0$ and let $P_n(q, t; x, y)$ be the generalized Eulerian polynomial.
There are natural numbers $c_{k,i,j}$, for $k, i, j \ge 0$, such that, writing
$\gamma_{n,k}(q, t) = \sum_{i=0}^{n} \sum_{j=0}^{n} c_{k,i,j} q^i t^j$, for all rational numbers
$q, t, x, y$ with $x \ne y$,
$$
P_n(q, t; x, y) = \sum_{k=0}^{\lfloor n/2 \rfloor} \gamma_{n,k}(q, t) x^k y^k (x + y)^{n - 2k}.
$$
That is, the gamma coefficients $\gamma_{n,k}$ are polynomials in $q$ and $t$ with nonnegative
integer coefficients.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 4
(`jis-2024-24.1.5-thm-4`). -/
public theorem generalizedEulerianP_gamma_nonneg (n : ℕ) :
    ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ q t x y : ℚ, x ≠ y →
      generalizedEulerianP q t x y n =
        ∑ k ∈ Finset.range (n / 2 + 1),
          (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (c k i j : ℚ) * q ^ i * t ^ j) * x ^ k * y ^ k * (x + y) ^ (n - 2 * k) := by
  exact ⟨generalizedEulerianP_gamma_nonneg.gammaCoeff n,
    fun q t x y hxy ↦ generalizedEulerianP_gamma_nonneg.grouped q t hxy n⟩

end

end MetaMathlibExt
