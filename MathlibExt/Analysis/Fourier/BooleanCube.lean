/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Fourier coefficients on the Boolean cube

The cube is represented by `Fin n → Bool`, with `true` representing `1` and
`false` representing `-1`. Fourier coefficients use the uniform probability measure.

The `FinsetFourier` section adds the `Finset`-indexed form of the same
transform (`fourierChar`/`fourierCoeff` over `E.powerset`), with bridges
(`fourierChar_eq_cubeChi`, `fourierCoeff_eq_boolFourierCoeff`) identifying
it with the canonical `Fin n` API after reindexing. The generic Fourier
laws for this transform — inversion (`fourier_inversion`) and Plancherel
(`fourier_plancherel`) — also live here, so callers needing only the
Fourier API do not import the KKL development.

These definitions are extracted, with their meanings unchanged, from
`OpenConjectures.ComputerScience.InversePolynomialInfluenceThreshold.Statement`,
originally formalized from the MFO-RIMS Tandem Workshop report, Oberwolfach Reports
(2025), DOI 10.4171/owr/2025/9, source record `OWR-14299088-012`.
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

/-- **Boolean cube.** For $n \in \mathbb{N}$, the Boolean cube of dimension $n$ is the set of
functions $x : \{0, \dots, n-1\} \to \{\mathrm{true}, \mathrm{false}\}$. It represents
$\{-1, 1\}^n$, with true standing for $1$ and false for $-1$. -/
abbrev BoolCube (n : ℕ) : Type := Fin n → Bool

/-- **Sign of a Boolean coordinate.** The sign of a Boolean value $b$ is the real number
$\sigma(b)$ given by $\sigma(\text{true}) = 1$ and $\sigma(\text{false}) = -1$. -/
def cubeVal : Bool → ℝ
  | true => 1
  | false => -1

/-- **Fourier character on the Boolean cube.** For a set $S$ of coordinates among $n$, the Fourier
character $\chi_S$ is the real-valued function on the Boolean cube in $n$ coordinates given by
$\chi_S(x) = \prod_{i \in S} \sigma(x_i)$, where $\sigma$ is the sign of a coordinate:
$\sigma(\text{true}) = 1$ and $\sigma(\text{false}) = -1$. -/
def cubeChi (n : ℕ) (S : Finset (Fin n)) (x : BoolCube n) : ℝ :=
  ∏ i ∈ S, cubeVal (x i)

/-- **Fourier coefficient on the Boolean cube.** For $n \in \mathbb{N}$, a function
$f : \{-1, 1\}^n \to \mathbb{R}$ and a set $S \subseteq \{0, \dots, n-1\}$, the normalized Fourier
coefficient of $f$ at $S$ is
$\hat f(S) = \frac{1}{|\{-1, 1\}^n|} \sum_{x \in \{-1, 1\}^n} f(x) \chi_S(x)$, where
$\chi_S(x) = \prod_{i \in S} x_i$. That is, $\hat f(S)$ is the uniform expectation of $f \chi_S$. -/
noncomputable def boolFourierCoeff (n : ℕ) (f : BoolCube n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (∑ x : BoolCube n, f x * cubeChi n S x) / (Fintype.card (BoolCube n) : ℝ)

/-- **Fourier degree at most $d$.** A real-valued function $f$ on the Boolean cube of dimension
$n$ has Fourier degree at most a natural number $d$ when its Fourier coefficient $\hat f(S)$
vanishes for every set $S$ of coordinates with $|S| > d$.

This is the degree of the multilinear polynomial representing the function on the cube. -/
def MultilinearDegreeLE (n : ℕ) (f : BoolCube n → ℝ) (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), d < S.card → boolFourierCoeff n f S = 0

/-- **Sign of true.** The sign $\sigma(\text{true})$ of the Boolean value true equals $1$. -/
@[simp] theorem cubeVal_true : cubeVal true = 1 := rfl

/-- **Sign of false.** The sign $\sigma(\text{false})$ of the Boolean value false equals $-1$. -/
@[simp] theorem cubeVal_false : cubeVal false = -1 := rfl

/-- **Coordinate signs square to one.** For every Boolean value $b$, its sign $\sigma(b)$ satisfies
$\sigma(b) \cdot \sigma(b) = 1$. -/
@[simp] theorem cubeVal_mul_self (b : Bool) : cubeVal b * cubeVal b = 1 := by
  cases b <;> simp

/-- **The empty Fourier character is constant one.** For every $n$ and every point $x$ of the
Boolean cube in $n$ coordinates, the Fourier character $\chi_\emptyset$ of the empty set of
coordinates satisfies $\chi_\emptyset(x) = 1$. -/
@[simp] theorem cubeChi_empty (n : ℕ) (x : BoolCube n) : cubeChi n ∅ x = 1 := by
  simp [cubeChi]

/-- **Singleton Fourier characters are coordinate signs.** For every $n$, every coordinate $i$ and
every point $x$ of the Boolean cube in $n$ coordinates, the Fourier character $\chi_{\{i\}}$ of
the singleton $\{i\}$ satisfies $\chi_{\{i\}}(x) = \sigma(x_i)$, where $\sigma$ is the sign of a
coordinate: $\sigma(\text{true}) = 1$ and $\sigma(\text{false}) = -1$. -/
@[simp] theorem cubeChi_singleton (n : ℕ) (i : Fin n) (x : BoolCube n) :
    cubeChi n {i} x = cubeVal (x i) := by
  simp [cubeChi]

/-- **Fourier characters square to one.** For every $n$, every set $S$ of the $n$ coordinates and
every point $x$ of the Boolean cube in $n$ coordinates, the Fourier character $\chi_S$ satisfies
$\chi_S(x) \cdot \chi_S(x) = 1$. -/
@[simp] theorem cubeChi_mul_self (n : ℕ) (S : Finset (Fin n)) (x : BoolCube n) :
    cubeChi n S x * cubeChi n S x = 1 := by
  simp only [cubeChi, ← Finset.prod_mul_distrib, cubeVal_mul_self, Finset.prod_const_one]

/-- **The empty Fourier coefficient is the mean.** For every $n \in \mathbb{N}$ and every function
$f : \{-1, 1\}^n \to \mathbb{R}$, the normalized Fourier coefficient of $f$ at the empty set is the
uniform mean of $f$: $\hat f(\emptyset) = \frac{1}{|\{-1, 1\}^n|} \sum_{x \in \{-1, 1\}^n} f(x)$. -/
theorem boolFourierCoeff_empty (n : ℕ) (f : BoolCube n → ℝ) :
    boolFourierCoeff n f ∅ = (∑ x : BoolCube n, f x) / (Fintype.card (BoolCube n) : ℝ) := by
  simp [boolFourierCoeff]

/-- **Fourier coefficients of the zero function.** For every $n \in \mathbb{N}$ and every
$S \subseteq \{0, \dots, n-1\}$, the normalized Fourier coefficient at $S$ of the identically zero
function on $\{-1, 1\}^n$ is $0$. -/
@[simp] theorem boolFourierCoeff_zero (n : ℕ) (S : Finset (Fin n)) :
    boolFourierCoeff n (fun _ => 0) S = 0 := by
  simp [boolFourierCoeff]

/-- **A character's own Fourier coefficient.** For every $n \in \mathbb{N}$ and every
$S \subseteq \{0, \dots, n-1\}$, the normalized Fourier coefficient at $S$ of the character
$\chi_S(x) = \prod_{i \in S} x_i$ on $\{-1, 1\}^n$ equals $1$, that is,
$\widehat{\chi_S}(S) = 1$. -/
@[simp] theorem boolFourierCoeff_cubeChi_self (n : ℕ) (S : Finset (Fin n)) :
    boolFourierCoeff n (cubeChi n S) S = 1 := by
  simp [boolFourierCoeff, Fintype.card_ne_zero]

/-- **Empty Fourier coefficient of a constant function.** For every $n \in \mathbb{N}$ and every
real $c$, the normalized Fourier coefficient at the empty set of the constant function
$x \mapsto c$ on the Boolean cube $\{-1, 1\}^n$ equals $c$. This includes dimension $n = 0$. -/
@[simp] theorem boolFourierCoeff_const_empty (n : ℕ) (c : ℝ) :
    boolFourierCoeff n (fun _ => c) ∅ = c := by
  simp [boolFourierCoeff, Fintype.card_ne_zero]

/-- **The zero function satisfies every Fourier degree bound.** For all natural numbers $n$ and
$d$, the zero function on the Boolean cube of dimension $n$ has Fourier degree at most $d$. -/
@[simp] theorem multilinearDegreeLE_zero (n d : ℕ) :
    MultilinearDegreeLE n (fun _ => 0) d := by
  intro S _
  simp

/-- **Fourier degree bounds are monotone.** Let $f$ be a real-valued function on the Boolean
cube of dimension $n$, and let $d \le e$ be natural numbers. If $f$ has Fourier degree at most
$d$, then $f$ has Fourier degree at most $e$. -/
theorem MultilinearDegreeLE.mono {n d e : ℕ} {f : BoolCube n → ℝ}
    (h : MultilinearDegreeLE n f d) (hde : d ≤ e) : MultilinearDegreeLE n f e := by
  intro S hS
  exact h S (lt_of_le_of_lt hde hS)

/-- **Fourier degree is at most the dimension.** Let $f$ be a real-valued function on the
Boolean cube of dimension $n$, and let $d \ge n$ be a natural number. Then $f$ has Fourier
degree at most $d$. -/
theorem multilinearDegreeLE_of_dimension_le {n d : ℕ} (f : BoolCube n → ℝ)
    (hnd : n ≤ d) : MultilinearDegreeLE n f d := by
  intro S hS
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  exact (Nat.not_lt_of_ge (hcard.trans hnd) hS).elim

/-- **Lagrange basis polynomial of a cube point.** Let $x$ be a point of the Boolean cube in $n$
coordinates, indexed by $i \in \{0, \dots, n-1\}$. Its cube basis polynomial is the real
polynomial $\prod_{i=0}^{n-1} \ell_i$ in the variables $X_0, \dots, X_{n-1}$, where $\ell_i = X_i$
if $x_i$ is true and $\ell_i = 1 - X_i$ if $x_i$ is false. Reading true as $1$ and false as $0$,
it is the Lagrange basis polynomial of $x$ on the grid $\{0,1\}^n$. -/
noncomputable def cubeBasis {n : ℕ}
    (x : BoolCube n) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin n,
    if x i then MvPolynomial.X i else 1 - MvPolynomial.X i

/-- **Multilinear extension.** Let $f$ be a Boolean-valued function on the Boolean cube of
dimension $n$, and read each coordinate and each value as $1$ for true and $0$ for false. The real
multilinear extension of $f$ is the polynomial in $\mathbb{R}[X_0, \dots, X_{n-1}]$
$$\sum_{x \in \{0,1\}^n} f(x) \prod_{i < n} \bigl(x_i X_i + (1 - x_i)(1 - X_i)\bigr).$$

For each cube point $x$ the product is its Lagrange basis polynomial: it evaluates to $1$ at $x$
and to $0$ at every other point of $\{0,1\}^n$. Hence the extension agrees with $f$ on
$\{0,1\}^n$, and it is the unique polynomial of degree at most one in each variable that does. -/
noncomputable def multilinearExtension {n : ℕ}
    (f : BoolCube n → Bool) : MvPolynomial (Fin n) ℝ := by
  classical
  exact
  ∑ x : BoolCube n,
    MvPolynomial.C (if f x then (1 : ℝ) else 0) *
      cubeBasis x

/-- **Lagrange basis polynomials on the cube are point indicators.** Let $x$ and $y$ be points
of the Boolean cube of dimension $n$, and identify $y$ with the point of
$\{0,1\}^n \subseteq \mathbb{R}^n$ whose $i$-th coordinate is $1$ when $y_i$ is true and $0$
when it is false. Then the cube basis polynomial of $x$ evaluated at $y$ equals $1$ if $x = y$
and $0$ otherwise. -/
theorem eval_cubeBasis {n : ℕ} (x y : BoolCube n) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) (cubeBasis x) =
      if x = y then 1 else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp only [cubeBasis, map_prod]
    apply Finset.prod_eq_one
    intro i _
    cases h : x i <;> simp [h]
  · simp only [cubeBasis, map_prod]
    rw [ite_eq_right hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hxi : x i <;> cases hyi : y i <;> simp_all

/-- **The multilinear extension agrees with its function on the cube.** Let $f$ be a Boolean
function on the Boolean cube of dimension $n$, and let $y$ be a point of the cube, identified
with the point of $\{0,1\}^n \subseteq \mathbb{R}^n$ whose $i$-th coordinate is $1$ when $y_i$
is true and $0$ when it is false. Then the real multilinear extension of $f$ evaluated at $y$
equals $1$ if $f(y)$ is true and $0$ if $f(y)$ is false. -/
theorem eval_multilinearExtension {n : ℕ}
    (f : BoolCube n → Bool) (y : BoolCube n) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0)
      (multilinearExtension f) = if f y then 1 else 0 := by
  classical
  simp only [multilinearExtension, map_sum, map_mul, MvPolynomial.eval_C]
  simp_rw [eval_cubeBasis]
  simp

private theorem sum_cubeBasis (n : ℕ) :
    ∑ x : BoolCube n, cubeBasis x = (1 : MvPolynomial (Fin n) ℝ) := by
  classical
  have h := Finset.sum_prod_piFinset (R := MvPolynomial (Fin n) ℝ)
    (Finset.univ : Finset Bool)
    (fun i b => if b then MvPolynomial.X i else 1 - MvPolynomial.X i)
  rw [Fintype.piFinset_univ] at h
  simpa [cubeBasis] using h

private theorem sum_projection_cubeBasis {n : ℕ} (i : Fin n) :
    ∑ x : BoolCube n,
      (if x i then (1 : MvPolynomial (Fin n) ℝ) else 0) * cubeBasis x =
        MvPolynomial.X i := by
  classical
  let g : Fin n → Bool → MvPolynomial (Fin n) ℝ := fun j b =>
    if b then MvPolynomial.X j else if j = i then 0 else 1 - MvPolynomial.X j
  have h := Finset.sum_prod_piFinset (R := MvPolynomial (Fin n) ℝ)
    (Finset.univ : Finset Bool) g
  rw [Fintype.piFinset_univ] at h
  have hl : (∑ x : BoolCube n, ∏ j, g j (x j)) =
      ∑ x : BoolCube n,
        (if x i then (1 : MvPolynomial (Fin n) ℝ) else 0) * cubeBasis x := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hxi : x i
    · simp only [hxi, ite_true, one_mul, g, cubeBasis]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [hxi, hji]
    · simp [hxi, g, Finset.prod_eq_zero (Finset.mem_univ i)]
  rw [hl] at h
  calc
    _ = ∏ j : Fin n,
        (MvPolynomial.X j + if j = i then 0 else 1 - MvPolynomial.X j) := by
      simpa [g] using h
    _ = ∏ j : Fin n,
        if j = i then MvPolynomial.X i else (1 : MvPolynomial (Fin n) ℝ) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j; simp
      · simp [hji]
    _ = MvPolynomial.X i := by simp

/-- **Multilinear extension of a constant function.** For every natural number $n$ and every
Boolean value $b$, the real multilinear extension of the constant function $b$ on the Boolean
cube of dimension $n$ is the constant polynomial $1$ if $b$ is true and the constant
polynomial $0$ if $b$ is false. -/
theorem multilinearExtension_const {n : ℕ} (b : Bool) :
    multilinearExtension (n := n) (fun _ => b) =
      MvPolynomial.C (if b then (1 : ℝ) else 0) := by
  classical
  cases b
  · simp [multilinearExtension]
  · simp [multilinearExtension, sum_cubeBasis]

/-- **Multilinear extension of a coordinate projection.** For every coordinate $i$ of the
Boolean cube of dimension $n$, the real multilinear extension of the projection $x \mapsto x_i$
is the variable $X_i$. -/
theorem multilinearExtension_projection {n : ℕ} (i : Fin n) :
    multilinearExtension (fun x => x i) = MvPolynomial.X i := by
  classical
  rw [multilinearExtension]
  convert sum_projection_cubeBasis i using 1
  apply Finset.sum_congr rfl
  intro x _
  cases x i <;> simp

/-- **Boolean degree.** Let $f$ be a Boolean-valued function on the Boolean cube in $n$
coordinates, and read true as $1$ and false as $0$. The Boolean degree of $f$ is the total degree
of the multilinear extension of $f$: the real multilinear polynomial in $n$ variables that takes
the value $f(x)$ at every point $x \in \{0,1\}^n$. -/
noncomputable def booleanDegree {n : ℕ}
    (f : BoolCube n → Bool) : ℕ :=
  (multilinearExtension f).totalDegree

/-- **Constant functions have Boolean degree zero.** For every $n \in \mathbb{N}$ and every Boolean
value $b$, the constant function $x \mapsto b$ on the Boolean cube of dimension $n$ has Boolean
degree $0$. -/
theorem booleanDegree_const {n : ℕ} (b : Bool) :
    booleanDegree (n := n) (fun _ => b) = 0 := by
  rw [booleanDegree, multilinearExtension_const]
  cases b <;> simp

/-- **Coordinate projections have Boolean degree one.** For every $n \in \mathbb{N}$ and every
$i < n$, the coordinate projection $x \mapsto x_i$ on the Boolean cube of dimension $n$ has
Boolean degree $1$. -/
theorem booleanDegree_projection {n : ℕ} (i : Fin n) :
    booleanDegree (fun x => x i) = 1 := by
  rw [booleanDegree, multilinearExtension_projection]
  simp

/-- **All-true function.** For $n \in \mathbb{N}$, the all-true function on the Boolean cube of
dimension $n$ is the Boolean AND of all coordinates: it sends $x = (x_0, \dots, x_{n-1})$ to true
exactly when $x_i$ is true for every $i < n$. In dimension $0$ it is constantly true. -/
def allTrueFunction {n : ℕ} (x : BoolCube n) : Bool :=
  decide (∀ i, x i = true)

private theorem sum_allTrue_cubeBasis (n : ℕ) :
    ∑ x : BoolCube n,
      (if allTrueFunction x then (1 : MvPolynomial (Fin n) ℝ) else 0) *
        cubeBasis x = ∏ i : Fin n, MvPolynomial.X i := by
  classical
  let g : Fin n → Bool → MvPolynomial (Fin n) ℝ := fun i b =>
    if b then MvPolynomial.X i else 0
  have h := Finset.sum_prod_piFinset (R := MvPolynomial (Fin n) ℝ)
    (Finset.univ : Finset Bool) g
  rw [Fintype.piFinset_univ] at h
  have hl : (∑ x : BoolCube n, ∏ i, g i (x i)) =
      ∑ x : BoolCube n,
        (if allTrueFunction x then (1 : MvPolynomial (Fin n) ℝ) else 0) *
          cubeBasis x := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ∀ i, x i = true
    · simp [allTrueFunction, hx, g, cubeBasis]
    · simp only [allTrueFunction, decide_eq_true_eq, hx, ite_false, zero_mul]
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [g, hi]
  rw [hl] at h
  simpa [g] using h

/-- **Multilinear extension of the AND function.** For every natural number $n$, the real
multilinear extension of the AND function on the Boolean cube of dimension $n$ (true exactly
when every coordinate is true) is the monomial $\prod_{i=0}^{n-1} X_i$. -/
theorem multilinearExtension_allTrue (n : ℕ) :
    multilinearExtension (n := n) allTrueFunction =
      ∏ i : Fin n, MvPolynomial.X i := by
  classical
  rw [multilinearExtension]
  convert sum_allTrue_cubeBasis n using 1
  apply Finset.sum_congr rfl
  intro x _
  cases allTrueFunction x <;> simp

/-- **The two-bit AND has Boolean degree two.** The all-true function on the Boolean cube of
dimension $2$, $(x_0, x_1) \mapsto x_0 \wedge x_1$, has Boolean degree $2$; that is, its real
multilinear extension has total degree $2$. -/
theorem booleanDegree_allTrue_two :
    booleanDegree (allTrueFunction (n := 2)) = 2 := by
  rw [booleanDegree, multilinearExtension_allTrue, Fin.prod_univ_two]
  simp [MvPolynomial.X, Finsupp.sum_add_index]

private theorem sum_ind_pow_mul_cubeChi_eq_zero {n : ℕ} (m : Fin n →₀ ℕ)
    (S : Finset (Fin n)) (hS : m.sum (fun _ e => e) < S.card) :
    (∑ x : BoolCube n,
      (∏ i, (if x i then (1 : ℝ) else 0) ^ m i) * cubeChi n S x) = 0 := by
  classical
  obtain ⟨i, hiS, hi0⟩ : ∃ i ∈ S, m i = 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : S ⊆ m.support := by
      intro j hj
      exact Finsupp.mem_support_iff.mpr (hcon j hj)
    have hle : S.card ≤ m.sum (fun _ e => e) := by
      rw [Finsupp.sum]
      calc S.card = ∑ _j ∈ S, 1 := by simp
        _ ≤ ∑ j ∈ S, m j :=
            Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.mpr (hcon j hj)
        _ ≤ ∑ j ∈ m.support, m j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => Nat.zero_le _)
    exact (Nat.not_lt_of_ge hle) hS
  have hfac : (∑ x : BoolCube n,
        (∏ i, (if x i then (1 : ℝ) else 0) ^ m i) * cubeChi n S x) =
      ∏ i, ∑ b : Bool,
        ((if b then (1 : ℝ) else 0) ^ m i *
          (if i ∈ S then cubeVal b else 1)) := by
    have h := Finset.sum_prod_piFinset (R := ℝ) (Finset.univ : Finset Bool)
      (fun i b => (if b then (1 : ℝ) else 0) ^ m i *
        (if i ∈ S then cubeVal b else 1))
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro x _
    have hchi : cubeChi n S x =
        ∏ i, (if i ∈ S then cubeVal (x i) else 1) := by
      simp [cubeChi, Finset.prod_ite_mem]
    rw [hchi, ← Finset.prod_mul_distrib]
  rw [hfac]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hsum : (∑ b : Bool,
      ((if b then (1 : ℝ) else 0) ^ m i *
        (if i ∈ S then cubeVal b else 1))) = 0 := by
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv, Finset.sum_pair (by decide : (false : Bool) ≠ true), hi0]
    simp [cubeVal, hiS]
  exact hsum

/-- **Fourier degree is at most Boolean degree.** Let $f$ be a Boolean function on the Boolean
cube of dimension $n$, and let $g$ be the real function with $g(x) = 1$ if $f(x)$ is true and
$g(x) = 0$ otherwise. Then $g$ has Fourier degree at most the Boolean degree of $f$: every
Fourier coefficient $\hat g(S)$ with $|S|$ greater than the total degree of the multilinear
extension of $f$ vanishes. -/
theorem multilinearDegreeLE_indicator {n : ℕ} (f : BoolCube n → Bool) :
    MultilinearDegreeLE n (fun x => if f x then (1 : ℝ) else 0)
      (booleanDegree f) := by
  classical
  intro S hS
  rw [boolFourierCoeff, div_eq_zero_iff]
  left
  have hsum : (∑ x : BoolCube n,
        (if f x then (1 : ℝ) else 0) * cubeChi n S x) =
      ∑ m ∈ (multilinearExtension f).support,
        (multilinearExtension f).coeff m *
          (∑ x : BoolCube n,
            (∏ i, (if x i then (1 : ℝ) else 0) ^ m i) * cubeChi n S x) := by
    have hpt : ∀ x : BoolCube n,
        (if f x then (1 : ℝ) else 0) * cubeChi n S x =
          ∑ m ∈ (multilinearExtension f).support,
            ((multilinearExtension f).coeff m *
              ∏ i, (if x i then (1 : ℝ) else 0) ^ m i) * cubeChi n S x := by
      intro x
      rw [← eval_multilinearExtension f x, MvPolynomial.eval_eq',
        Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_assoc]
  rw [hsum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [sum_ind_pow_mul_cubeChi_eq_zero m S
    (lt_of_le_of_lt (MvPolynomial.le_totalDegree hm) hS)]
  simp

section FinsetFourier

variable {ι : Type*} [DecidableEq ι]

/-- The Fourier character on the subset lattice: `χ_S(T) = (−1)^|S ∩ T|`.
This is the `Finset`-indexed form of the uniform-cube transform;
`fourierChar_eq_cubeChi` identifies it with the canonical `cubeChi`
after reindexing. -/
noncomputable def fourierChar (S T : Finset ι) : ℝ :=
  (-1 : ℝ) ^ (S ∩ T).card

/-- The Fourier coefficient `f̂(S)`: the uniform average of `f · χ_S`
over the cube. `fourierCoeff_eq_boolFourierCoeff` identifies it with
the canonical `boolFourierCoeff` after reindexing. -/
noncomputable def fourierCoeff (E : Finset ι) (f : Finset ι → ℝ)
    (S : Finset ι) : ℝ :=
  (∑ U ∈ E.powerset, f U * fourierChar S U) / 2 ^ E.card

/-- The `n`-cube has `2 ^ n` points. -/
theorem card_boolCube (n : ℕ) : Fintype.card (BoolCube n) = 2 ^ n := by
  change Fintype.card (Fin n → Bool) = 2 ^ n
  rw [Fintype.card_pi, Finset.prod_const, Fintype.card_bool,
    Finset.card_univ, Fintype.card_fin]

/-- Subsets of `E` are indicator functions on `E` (members read `false`,
matching `cubeVal false = -1`). -/
noncomputable def powersetEquivIndicator (E : Finset ι) :
    ↥E.powerset ≃ (↥E → Bool) where
  toFun S i := decide (i.val ∉ S.val)
  invFun b :=
    ⟨E.filter (fun a => if h : a ∈ E then b ⟨a, h⟩ = false else False),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  left_inv S := by
    obtain ⟨T, hT⟩ := S
    have hsub : T ⊆ E := Finset.mem_powerset.mp hT
    refine Subtype.ext ?_
    change E.filter (fun a =>
      if _h : a ∈ E then decide (a ∉ T) = false else False) = T
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨haE, hdec⟩
      rw [dite_eq_left haE] at hdec
      revert hdec
      by_cases haT : a ∈ T
      · intro _; exact haT
      · intro hdec; simp [haT] at hdec
    · intro haT
      refine ⟨hsub haT, ?_⟩
      rw [dite_eq_left (hsub haT)]
      show decide (a ∉ T) = false
      simp [haT]
  right_inv b := by
    funext i
    change decide (i.val ∉ E.filter
      (fun a => if h : a ∈ E then b ⟨a, h⟩ = false else False)) = b i
    have h2 : (i.val ∈ E ∧
          (if h : i.val ∈ E then b ⟨i.val, h⟩ = false else False))
        ↔ b i = false := by
      constructor
      · rintro ⟨-, hite⟩
        rw [dite_eq_left i.property] at hite
        exact hite
      · intro hbi
        refine ⟨i.property, ?_⟩
        rw [dite_eq_left i.property]
        exact hbi
    have hmem : (i.val ∉ E.filter
          (fun a => if h : a ∈ E then b ⟨a, h⟩ = false else False))
        ↔ b i = true := by
      simp only [Finset.mem_filter, h2]
      cases b i <;> simp
    simp only [hmem]
    cases b i <;> simp

/-- The cube over `E`, reindexed by `Fin E.card`. -/
noncomputable def powersetEquivBoolCube (E : Finset ι) :
    ↥E.powerset ≃ BoolCube E.card :=
  (powersetEquivIndicator E).trans
    ((Finset.equivFin E).arrowCongr (Equiv.refl Bool))

/-- Applying the reindexing equivalence reads off subset membership. -/
theorem powersetEquivBoolCube_apply (E : Finset ι) (T : Finset ι)
    (hT : T ∈ E.powerset) (j : Fin E.card) :
    powersetEquivBoolCube E ⟨T, hT⟩ j
      = decide (((Finset.equivFin E).symm j).val ∉ T) := rfl

/-- Reindex a sub-cube of `E` as a `Fin`-indexed set. -/
noncomputable def reindexFinset (E S : Finset ι) (hS : S ⊆ E) :
    Finset (Fin E.card) :=
  S.attach.map
    ⟨fun a => Finset.equivFin E ⟨a.val, hS a.property⟩,
      fun a b h => by
        have h' := (Finset.equivFin E).injective h
        simp only [Subtype.mk.injEq] at h'
        exact Subtype.ext h'⟩

/-- Decode a `Fin`-indexed cube point back to a subset of `E`. -/
noncomputable def decodeBoolCube (E : Finset ι) (x : BoolCube E.card) :
    Finset ι :=
  ((powersetEquivBoolCube E).symm x).val

/-- Decoding after encoding is the identity. -/
@[simp] theorem decode_encode (E : Finset ι) (T : Finset ι)
    (hT : T ∈ E.powerset) :
    decodeBoolCube E (powersetEquivBoolCube E ⟨T, hT⟩) = T := by
  have h : (powersetEquivBoolCube E).symm
      ((powersetEquivBoolCube E) ⟨T, hT⟩) = ⟨T, hT⟩ :=
    Equiv.symm_apply_apply _ _
  exact congrArg Subtype.val h

/-- A product of membership-gated signs is a parity power. -/
private theorem prod_ite_neg_one (S T : Finset ι) :
    ∏ a ∈ S, (if a ∈ T then (-1 : ℝ) else 1)
      = (-1 : ℝ) ^ (S ∩ T).card := by
  have hsplit : (∏ x ∈ S.filter (· ∈ T),
          (if x ∈ T then (-1 : ℝ) else 1))
        * ∏ x ∈ S.filter (fun x => ¬x ∈ T),
          (if x ∈ T then (-1 : ℝ) else 1)
      = ∏ x ∈ S, (if x ∈ T then (-1 : ℝ) else 1) :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hpos : ∏ a ∈ S.filter (· ∈ T),
      (if a ∈ T then (-1 : ℝ) else 1)
      = (-1 : ℝ) ^ (S ∩ T).card := by
    rw [Finset.prod_congr rfl
      (fun a ha => ite_eq_left (Finset.mem_filter.mp ha).2),
      Finset.prod_const, Finset.filter_mem_eq_inter]
  have hneg : ∏ a ∈ S.filter (fun a => a ∉ T),
      (if a ∈ T then (-1 : ℝ) else 1) = 1 :=
    Finset.prod_eq_one (fun a ha => ite_eq_right (Finset.mem_filter.mp ha).2)
  rw [← hsplit, hpos, hneg, mul_one]

/-- Reindexing identifies `fourierChar` with the canonical `cubeChi`. -/
theorem fourierChar_eq_cubeChi (E : Finset ι) (S T : Finset ι)
    (hS : S ⊆ E) (hT : T ∈ E.powerset) :
    fourierChar S T
      = cubeChi E.card (reindexFinset E S hS)
        (powersetEquivBoolCube E ⟨T, hT⟩) := by
  have hfactor : ∀ a ∈ S.attach,
      cubeVal (powersetEquivBoolCube E ⟨T, hT⟩
        (Finset.equivFin E ⟨a.val, hS a.property⟩))
        = (if a.val ∈ T then (-1 : ℝ) else 1) := by
    intro a _
    rw [powersetEquivBoolCube_apply E T hT, Equiv.symm_apply_apply]
    by_cases haT : a.val ∈ T <;> simp [haT, cubeVal]
  have hprod : (∏ x ∈ S.attach, cubeVal
        (powersetEquivBoolCube E ⟨T, hT⟩
          (Finset.equivFin E ⟨x.val, hS x.property⟩)))
      = ∏ a ∈ S, (if a ∈ T then (-1 : ℝ) else 1) := by
    have h1 : (∏ x ∈ S.attach, cubeVal
          (powersetEquivBoolCube E ⟨T, hT⟩
            (Finset.equivFin E ⟨x.val, hS x.property⟩)))
        = ∏ x ∈ S.attach,
          (fun a : ι => if a ∈ T then (-1 : ℝ) else 1) x.val :=
      Finset.prod_congr rfl (fun a _ => hfactor a (Finset.mem_attach S a))
    rw [h1]
    exact Finset.prod_attach S (fun a => if a ∈ T then (-1 : ℝ) else 1)
  have hmap : cubeChi E.card (reindexFinset E S hS)
        (powersetEquivBoolCube E ⟨T, hT⟩)
      = ∏ x ∈ S.attach, cubeVal
        (powersetEquivBoolCube E ⟨T, hT⟩
          (Finset.equivFin E ⟨x.val, hS x.property⟩)) := by
    exact Finset.prod_map S.attach _ _
  calc fourierChar S T = (-1 : ℝ) ^ (S ∩ T).card := rfl
    _ = ∏ a ∈ S, (if a ∈ T then (-1 : ℝ) else 1) :=
        (prod_ite_neg_one S T).symm
    _ = ∏ x ∈ S.attach, cubeVal
          (powersetEquivBoolCube E ⟨T, hT⟩
            (Finset.equivFin E ⟨x.val, hS x.property⟩)) := hprod.symm
    _ = cubeChi E.card (reindexFinset E S hS)
          (powersetEquivBoolCube E ⟨T, hT⟩) := hmap.symm

omit [DecidableEq ι] in
/-- A powerset sum is a sum over the coerced type. -/
private theorem sum_powerset_coe (E : Finset ι) (g : Finset ι → ℝ) :
    (∑ U : ↥E.powerset, g U.val) = ∑ U ∈ E.powerset, g U := by
  conv_lhs => rw [Finset.univ_eq_attach E.powerset]
  exact Finset.sum_attach _ _

/-- Reindexing identifies `fourierCoeff` with the canonical
`boolFourierCoeff`. -/
theorem fourierCoeff_eq_boolFourierCoeff (E : Finset ι)
    (f : Finset ι → ℝ) (S : Finset ι) (hS : S ⊆ E) :
    fourierCoeff E f S
      = boolFourierCoeff E.card (fun x => f (decodeBoolCube E x))
        (reindexFinset E S hS) := by
  have hcard : (Fintype.card (BoolCube E.card) : ℝ) = 2 ^ E.card := by
    exact_mod_cast card_boolCube E.card
  have hsum : (∑ U ∈ E.powerset, f U * fourierChar S U)
      = ∑ x : BoolCube E.card,
        f (decodeBoolCube E x)
          * cubeChi E.card (reindexFinset E S hS) x := by
    calc (∑ U ∈ E.powerset, f U * fourierChar S U)
        = ∑ U : ↥E.powerset,
          (fun V => f V * fourierChar S V) U.val :=
            (sum_powerset_coe E _).symm
      _ = ∑ x : BoolCube E.card,
          f (decodeBoolCube E x)
            * cubeChi E.card (reindexFinset E S hS) x :=
            Fintype.sum_equiv _ _ _ (fun U => by
              obtain ⟨T, hT⟩ := U
              change f T * fourierChar S T
                = f (decodeBoolCube E (powersetEquivBoolCube E ⟨T, hT⟩))
                  * cubeChi E.card (reindexFinset E S hS)
                    (powersetEquivBoolCube E ⟨T, hT⟩)
              rw [decode_encode E T hT,
                fourierChar_eq_cubeChi E S T hS hT])
  unfold fourierCoeff boolFourierCoeff
  rw [hcard, hsum]

section FourierLaws

/-- Characters are symmetric in the two arguments. -/
private theorem fourierChar_comm (S T : Finset ι) :
    fourierChar S T = fourierChar T S := by
  unfold fourierChar
  rw [Finset.inter_comm]

/-- Even shifts do not change a `−1` power. -/
private theorem neg_one_pow_add_mul_two (c k : ℕ) :
    (-1 : ℝ) ^ (c + 2 * k) = (-1 : ℝ) ^ c := by
  rw [pow_add]
  have h2 : (-1 : ℝ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    norm_num
  rw [h2, mul_one]

/-- Parity identity behind character multiplicativity, from disjoint
card decompositions. -/
private theorem card_inter_add_card_inter (S U T : Finset ι) :
    (S ∩ T).card + (U ∩ T).card
      = (((S \ U) ∪ (U \ S)) ∩ T).card + 2 * ((S ∩ U) ∩ T).card := by
  have hunion1 : (S \ U) ∩ T ∪ (S ∩ U) ∩ T = S ∩ T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisj1 : Disjoint ((S \ U) ∩ T) ((S ∩ U) ∩ T) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter] at hx1 hx2
    obtain ⟨hxSU, -⟩ := hx1
    obtain ⟨hxIU, -⟩ := hx2
    exact (Finset.mem_sdiff.mp hxSU).2 (Finset.mem_inter.mp hxIU).2
  have h1 : (S ∩ T).card
      = ((S \ U) ∩ T).card + ((S ∩ U) ∩ T).card := by
    rw [← hunion1, Finset.card_union_of_disjoint hdisj1]
  have hunion2 : (U \ S) ∩ T ∪ (S ∩ U) ∩ T = U ∩ T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisj2 : Disjoint ((U \ S) ∩ T) ((S ∩ U) ∩ T) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter] at hx1 hx2
    obtain ⟨hxUS, -⟩ := hx1
    obtain ⟨hxIU, -⟩ := hx2
    exact (Finset.mem_sdiff.mp hxUS).2 (Finset.mem_inter.mp hxIU).1
  have h2 : (U ∩ T).card
      = ((U \ S) ∩ T).card + ((S ∩ U) ∩ T).card := by
    rw [← hunion2, Finset.card_union_of_disjoint hdisj2]
  have hunion3 : (S \ U) ∩ T ∪ (U \ S) ∩ T
      = ((S \ U) ∪ (U \ S)) ∩ T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisj3 : Disjoint ((S \ U) ∩ T) ((U \ S) ∩ T) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter] at hx1 hx2
    obtain ⟨hxSU, -⟩ := hx1
    obtain ⟨hxUS, -⟩ := hx2
    exact (Finset.mem_sdiff.mp hxSU).2 (Finset.mem_sdiff.mp hxUS).1
  have h3 : (((S \ U) ∪ (U \ S)) ∩ T).card
      = ((S \ U) ∩ T).card + ((U \ S) ∩ T).card := by
    rw [← hunion3, Finset.card_union_of_disjoint hdisj3]
  omega

/-- Characters multiply by symmetric difference. -/
private theorem fourierChar_mul (S U T : Finset ι) :
    fourierChar S T * fourierChar U T
      = fourierChar ((S \ U) ∪ (U \ S)) T := by
  unfold fourierChar
  rw [← pow_add, card_inter_add_card_inter S U T]
  exact neg_one_pow_add_mul_two _ _

/-- Inserting a fresh element of `V` flips the sign of `χ_V`. -/
private theorem fourierChar_insert_of_mem_of_notMem (V S : Finset ι) (v : ι)
    (hvV : v ∈ V) (hvS : v ∉ S) :
    fourierChar V (insert v S) = -fourierChar V S := by
  have hinter : V ∩ insert v S = insert v (V ∩ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hxV, rfl | hxS⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hxV, hxS⟩
    · rintro (rfl | ⟨hxV, hxS⟩)
      · exact ⟨hvV, Or.inl rfl⟩
      · exact ⟨hxV, Or.inr hxS⟩
  have hnot : v ∉ V ∩ S := fun h => hvS (Finset.mem_inter.mp h |>.2)
  unfold fourierChar
  rw [hinter, Finset.card_insert_of_notMem hnot, pow_succ]
  ring

/-- Character sums over the cube: `∑ T, χ_V T` is `2 ^ |E|` if
`V ∩ E = ∅` and `0` otherwise (toggle-pairing). -/
private theorem sum_fourierChar (E V : Finset ι) :
    ∑ T ∈ E.powerset, fourierChar V T
      = if V ∩ E = ∅ then (2 ^ E.card : ℝ) else 0 := by
  by_cases hVE : V ∩ E = ∅
  · rw [ite_eq_left hVE]
    have hterm : ∀ T ∈ E.powerset, fourierChar V T = 1 := by
      intro T hT
      have hsub : V ∩ T ⊆ V ∩ E :=
        Finset.inter_subset_inter (fun _ hx => hx)
          (Finset.mem_powerset.mp hT)
      rw [hVE] at hsub
      have hcard : (V ∩ T).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.subset_empty.mp hsub)
      unfold fourierChar
      rw [hcard, pow_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_powerset]
    norm_num
  · rw [ite_eq_right hVE]
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hVE
    have hvV : v ∈ V := (Finset.mem_inter.mp hv).1
    have hvE : v ∈ E := (Finset.mem_inter.mp hv).2
    have hE : E = insert v (E.erase v) := (Finset.insert_erase hvE).symm
    have hne : v ∉ E.erase v := Finset.notMem_erase v E
    rw [hE, Finset.sum_powerset_insert hne, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun S hS => ?_)
    have hvS : v ∉ S :=
      fun h => hne ((Finset.mem_powerset.mp hS) h)
    rw [fourierChar_insert_of_mem_of_notMem V S v hvV hvS]
    ring

/-- Orthogonality of distinct characters over the cube. -/
private theorem sum_fourierChar_mul (E S U : Finset ι) :
    ∑ T ∈ E.powerset, (fourierChar S T * fourierChar U T)
      = if ((S \ U) ∪ (U \ S)) ∩ E = ∅ then (2 ^ E.card : ℝ) else 0 := by
  have h : ∀ T ∈ E.powerset,
      fourierChar S T * fourierChar U T
        = fourierChar ((S \ U) ∪ (U \ S)) T :=
    fun T _ => fourierChar_mul S U T
  rw [Finset.sum_congr rfl h]
  exact sum_fourierChar E _

omit [DecidableEq ι] in
/-- `2 ^ |E|` as a real is nonzero. -/
private theorem two_pow_card_ne_zero (E : Finset ι) :
    (2 ^ E.card : ℝ) ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-- Clearing the denominator of a Fourier coefficient. -/
private theorem fourierCoeff_mul_two_pow (E : Finset ι) (f : Finset ι → ℝ)
    (S : Finset ι) :
    fourierCoeff E f S * 2 ^ E.card
      = ∑ U ∈ E.powerset, f U * fourierChar S U := by
  unfold fourierCoeff
  exact div_mul_cancel₀ _ (two_pow_card_ne_zero E)

/-- The symmetric difference of two subcubes of `E` meets `E` trivially
iff the two sets agree. -/
private theorem symmDiff_inter_eq_empty_iff (E S U : Finset ι)
    (hS : S ∈ E.powerset) (hU : U ∈ E.powerset) :
    ((S \ U) ∪ (U \ S)) ∩ E = ∅ ↔ S = U := by
  constructor
  · intro h
    have hS' : S ⊆ E := Finset.mem_powerset.mp hS
    have hU' : U ⊆ E := Finset.mem_powerset.mp hU
    ext x
    constructor
    · intro hxS
      by_contra hxU
      have hmem : x ∈ ((S \ U) ∪ (U \ S)) ∩ E :=
        Finset.mem_inter.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxS, hxU⟩),
            hS' hxS⟩
      rw [h] at hmem
      exact Finset.notMem_empty x hmem
    · intro hxU
      by_contra hxS
      have hmem : x ∈ ((S \ U) ∪ (U \ S)) ∩ E :=
        Finset.mem_inter.mpr
          ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxU, hxS⟩),
            hU' hxU⟩
      rw [h] at hmem
      exact Finset.notMem_empty x hmem
  · intro h
    subst h
    have : ((S \ S) ∪ (S \ S)) ∩ E = ∅ := by simp
    exact this

/-- Fourier inversion on the cube. -/
public theorem fourier_inversion (E : Finset ι) (f : Finset ι → ℝ)
    (T : Finset ι) (hT : T ∈ E.powerset) :
    f T = ∑ S ∈ E.powerset, fourierCoeff E f S * fourierChar S T := by
  have horth : ∀ U ∈ E.powerset,
      (∑ S ∈ E.powerset, fourierChar U S * fourierChar T S)
        = (if U = T then (2 ^ E.card : ℝ) else 0) := by
    intro U hU
    rw [sum_fourierChar_mul E U T]
    by_cases hUT : U = T
    · subst hUT
      have hempty : ((U \ U) ∪ (U \ U)) ∩ E = ∅ := by simp
      rw [ite_eq_left hempty, ite_eq_left rfl]
    · have hne : ((U \ T) ∪ (T \ U)) ∩ E ≠ ∅ := by
        intro hcon
        exact hUT ((symmDiff_inter_eq_empty_iff E U T hU hT).mp hcon)
      rw [ite_eq_right hne, ite_eq_right hUT]
  have hswap : (∑ S ∈ E.powerset, ∑ U ∈ E.powerset,
        f U * (fourierChar S U * fourierChar S T))
      = ∑ U ∈ E.powerset, f U * (∑ S ∈ E.powerset,
        fourierChar S U * fourierChar S T) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    rw [Finset.mul_sum]
  have hinner : ∀ U ∈ E.powerset,
      (∑ S ∈ E.powerset, fourierChar S U * fourierChar S T)
        = (if U = T then (2 ^ E.card : ℝ) else 0) := by
    intro U hU
    have hcomm : ∀ S ∈ E.powerset,
        fourierChar S U * fourierChar S T
          = fourierChar U S * fourierChar T S := by
      intro S _
      rw [fourierChar_comm S U, fourierChar_comm S T]
    rw [Finset.sum_congr rfl hcomm]
    exact horth U hU
  have hsum : (∑ S ∈ E.powerset, ∑ U ∈ E.powerset,
        f U * (fourierChar S U * fourierChar S T))
      = f T * 2 ^ E.card := by
    rw [hswap]
    have hred : ∀ U ∈ E.powerset,
        f U * (∑ S ∈ E.powerset, fourierChar S U * fourierChar S T)
          = (if U = T then f U * 2 ^ E.card else 0) := by
      intro U hU
      rw [hinner U hU]
      by_cases hUT : U = T <;> simp [hUT]
    rw [Finset.sum_congr rfl hred, Finset.sum_ite_eq' _ T _,
      ite_eq_left hT]
  have hexpand : (∑ S ∈ E.powerset, fourierCoeff E f S * fourierChar S T)
        * 2 ^ E.card
      = f T * 2 ^ E.card := by
    have hterm : ∀ S ∈ E.powerset,
        (fourierCoeff E f S * fourierChar S T) * 2 ^ E.card
          = ∑ U ∈ E.powerset, f U * (fourierChar S U * fourierChar S T) := by
      intro S _
      have h1 : (fourierCoeff E f S * fourierChar S T) * 2 ^ E.card
          = (fourierCoeff E f S * 2 ^ E.card) * fourierChar S T := by
        ring
      rw [h1, fourierCoeff_mul_two_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun U _ => ?_)
      ring
    rw [Finset.sum_mul, Finset.sum_congr rfl hterm]
    exact hsum
  have hne := two_pow_card_ne_zero E
  have hcancel : (∑ S ∈ E.powerset, fourierCoeff E f S * fourierChar S T)
        * 2 ^ E.card = f T * 2 ^ E.card := hexpand
  have := mul_right_cancel₀ hne hcancel
  exact this.symm

/-- Plancherel on the cube: the mean square equals the sum of squared
Fourier coefficients. -/
public theorem fourier_plancherel (E : Finset ι) (f : Finset ι → ℝ) :
    (∑ T ∈ E.powerset, f T ^ 2) / 2 ^ E.card
      = ∑ S ∈ E.powerset, fourierCoeff E f S ^ 2 := by
  have hT : ∀ T ∈ E.powerset,
      f T ^ 2 = ∑ S ∈ E.powerset,
        fourierCoeff E f S * (f T * fourierChar S T) := by
    intro T hT
    have hinv := fourier_inversion E f T hT
    have hsq : f T ^ 2 = f T * f T := by ring
    rw [hsq, hinv, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring
  have hswap : (∑ T ∈ E.powerset, ∑ S ∈ E.powerset,
        fourierCoeff E f S * (f T * fourierChar S T))
      = (∑ S ∈ E.powerset, fourierCoeff E f S ^ 2) * 2 ^ E.card := by
    rw [Finset.sum_comm]
    have hS : ∀ S ∈ E.powerset,
        (∑ T ∈ E.powerset, fourierCoeff E f S * (f T * fourierChar S T))
          = fourierCoeff E f S ^ 2 * 2 ^ E.card := by
      intro S _
      have h1 : (∑ T ∈ E.powerset, fourierCoeff E f S * (f T * fourierChar S T))
          = fourierCoeff E f S * (fourierCoeff E f S * 2 ^ E.card) := by
        have hfac : (∑ T ∈ E.powerset,
              fourierCoeff E f S * (f T * fourierChar S T))
            = fourierCoeff E f S
              * (∑ T ∈ E.powerset, f T * fourierChar S T) := by
          rw [Finset.mul_sum]
        rw [hfac, ← fourierCoeff_mul_two_pow]
      rw [h1]
      ring
    rw [Finset.sum_congr rfl hS, Finset.sum_mul]
  have htot : (∑ T ∈ E.powerset, f T ^ 2)
      = (∑ S ∈ E.powerset, fourierCoeff E f S ^ 2) * 2 ^ E.card := by
    rw [Finset.sum_congr rfl hT]
    exact hswap
  rw [htot]
  exact mul_div_cancel_right₀ _ (two_pow_card_ne_zero E)

end FourierLaws

end FinsetFourier

end BooleanCube
