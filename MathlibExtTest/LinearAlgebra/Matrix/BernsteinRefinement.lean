/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.BernsteinRefinement
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Matrix MvPolynomial

example {ι m : Type*} [Fintype ι] {n d : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} {L : Matrix m m ℝ}
    (hp : ∀ a b i, (P a b).degreeOf i ≤ n i) (hnd : ∀ i, n i ≤ d i)
    (hc : ∀ k : ι → ℕ, (∀ i, k i ≤ n i) → (Matrix.bernsteinCoeff n P k - L).PosSemidef)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ d i) :
    (Matrix.bernsteinCoeff d P k - L).PosSemidef := by
  exact Matrix.posSemidef_bernsteinCoeff_sub_of_le hp hnd hc k hk

example {ι m : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (r : ι) (t : ℝ) (ht : t ∈ Set.Icc 0 1) {c : (ι → ℕ) → Matrix m m ℝ}
    {L : Matrix m m ℝ}
    (hc : ∀ k, (∀ i, k i ≤ n i) → (c k - L).PosSemidef)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n i) :
    (Matrix.bernsteinSubdivideLeft r t c k - L).PosSemidef := by
  exact Matrix.posSemidef_bernsteinSubdivideLeft_sub ht hc k hk

-- A fixed non-diagonal lower bound need not itself be positive semidefinite.
private def lower : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 1; 1, -3]

private noncomputable def net (k : Fin 2 → ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  lower + ((k 0 : ℝ)^2 + k 1) • 1

private theorem net_bound (k : Fin 2 → ℕ) : (net k - lower).PosSemidef := by
  simpa only [net, add_sub_cancel_left] using
    (Matrix.PosSemidef.one.smul (by positivity : 0 ≤ (k 0 : ℝ)^2 + k 1) :
      (((k 0 : ℝ)^2 + k 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef)

-- An asymmetric cut distinguishes left and right index conventions.
example : Matrix.bernsteinSubdivideLeft 0 (1/3) net ![2, 1] =
    !![-1/9, 1; 1, -10/9] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.bernsteinSubdivideLeft, MvPolynomial.bernsteinSubdivideLeft,
      bernsteinPolynomial.deCasteljau, net, lower, Function.update, Matrix.add_apply,
      Matrix.smul_apply]

example : Matrix.bernsteinSubdivideRight ![2, 1] 0 (1/3) net ![1, 0] =
    !![0, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.bernsteinSubdivideRight, MvPolynomial.bernsteinSubdivideRight,
      bernsteinPolynomial.deCasteljau, net, lower, Function.update, Matrix.add_apply,
      Matrix.smul_apply]

-- The same fixed lower bound survives on both child expansions, at every
-- cube point; all coefficient hypotheses are discharged for this concrete net.
example (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) :
    ((Matrix.bernsteinExpansion ![2, 1]
      (Matrix.bernsteinSubdivideLeft 0 (1/3) net)).map (eval x) - lower).PosSemidef ∧
    ((Matrix.bernsteinExpansion ![2, 1]
      (Matrix.bernsteinSubdivideRight ![2, 1] 0 (1/3) net)).map (eval x) - lower).PosSemidef := by
  constructor
  · exact Matrix.posSemidef_map_eval_bernsteinExpansion_sub hx
      (Matrix.posSemidef_bernsteinSubdivideLeft_sub (by norm_num) (fun k _ => net_bound k))
  · exact Matrix.posSemidef_map_eval_bernsteinExpansion_sub hx
      (Matrix.posSemidef_bernsteinSubdivideRight_sub (by norm_num) (fun k _ => net_bound k))

example (c : (Fin 2 → ℕ) → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.bernsteinSubdivideLeft 0 0 c ![2, 1] = c ![0, 1] ∧
    Matrix.bernsteinSubdivideRight ![2, 1] 0 1 c ![0, 1] = c ![2, 1] := by
  constructor <;> ext i j <;>
    norm_num [Matrix.bernsteinSubdivideLeft, Matrix.bernsteinSubdivideRight,
      MvPolynomial.bernsteinSubdivideLeft, MvPolynomial.bernsteinSubdivideRight,
      bernsteinPolynomial.deCasteljau, Function.update]
  all_goals congr 1; funext l; fin_cases l <;> simp [Function.update]

-- A degree-zero direction is unchanged for arbitrary cuts, including cuts
-- outside the range required for convexity.
example (t : ℝ) (c : (Fin 2 → ℕ) → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.bernsteinSubdivideLeft 0 t c ![0, 2] = c ![0, 2] ∧
    Matrix.bernsteinSubdivideRight ![0, 3] 0 t c ![0, 2] = c ![0, 2] := by
  constructor <;> ext i j <;>
    norm_num [Matrix.bernsteinSubdivideLeft, Matrix.bernsteinSubdivideRight,
      MvPolynomial.bernsteinSubdivideLeft, MvPolynomial.bernsteinSubdivideRight,
      bernsteinPolynomial.deCasteljau, Function.update]
  all_goals congr 1; funext l; fin_cases l <;> simp [Function.update]

example {P : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℝ)}
    {n : Fin 2 → ℕ} {c : (Fin 2 → ℕ) → Matrix (Fin 2) (Fin 2) ℝ}
    {a b x : Fin 2 → ℝ} {L : Matrix (Fin 2) (Fin 2) ℝ}
    (hrep : Matrix.bernsteinExpansion n c = P.map (boxPullback a b))
    (hx : ∀ i, x i ∈ Set.Icc (a i) (b i))
    (hc : ∀ k, (∀ i, k i ≤ n i) → (c k - L).PosSemidef) :
    (P.map (eval x) - L).PosSemidef := by
  exact Matrix.posSemidef_map_eval_sub_of_bernsteinExpansion_box hrep hx hc

private noncomputable def affine : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 2) ℝ) :=
  fun _ _ => C 2 + monomial (Finsupp.single 0 1) 1

private theorem affine_degree (a b : Fin 1) (i : Fin 2) :
    (affine a b).degreeOf i ≤ ![1, 0] i := by
  apply (degreeOf_add_le _ _ _).trans
  apply max_le (by simp)
  rw [degreeOf_monomial_eq _ _ (by norm_num)]
  fin_cases i <;> simp

-- The untouched zero-degree coordinate is elevated too; inspect an interior
-- coefficient at degree (3,2), not just the endpoint cases of the recurrence.
example : Matrix.bernsteinCoeff ![3, 2] affine ![1, 2] = !![(7/3 : ℝ)] := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.bernsteinCoeff_apply, affine, MvPolynomial.bernsteinCoeff_add,
    MvPolynomial.bernsteinCoeff_monomial, Fin.prod_univ_two, Finsupp.single_apply]

example (k : Fin 2 → ℕ) (hk : ∀ i, k i ≤ ![3, 2] i) :
    (Matrix.bernsteinCoeff ![3, 2] affine k - (2 : ℝ) • 1).PosSemidef := by
  apply Matrix.posSemidef_bernsteinCoeff_sub_of_le affine_degree
    (by intro i; fin_cases i <;> norm_num) _ k hk
  intro j _
  have heq : Matrix.bernsteinCoeff ![1, 0] affine j - (2 : ℝ) • 1 =
      (j 0 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext a b
    fin_cases a; fin_cases b
    norm_num [Matrix.bernsteinCoeff_apply, affine, MvPolynomial.bernsteinCoeff_add,
      MvPolynomial.bernsteinCoeff_monomial, Fin.prod_univ_two, Finsupp.single_apply,
      Matrix.sub_apply, Matrix.smul_apply, Nat.choose_one_right]
  rw [heq]
  exact Matrix.PosSemidef.one.smul (by positivity)

-- Empty variables and degree zero are genuine constant-polynomial cases.
example (k : Fin 0 → ℕ) :
    (Matrix.bernsteinCoeff (fun _ => 0)
      (Matrix.of (fun (_ _ : Fin 1) => (C 3 : MvPolynomial (Fin 0) ℝ))) k -
      (2 : ℝ) • 1).PosSemidef := by
  apply Matrix.posSemidef_bernsteinCoeff_sub_of_le (n := fun _ => 0)
    (by intro a b i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i) _ k
    (by intro i; exact Fin.elim0 i)
  intro j _
  have heq : Matrix.bernsteinCoeff (fun (_ : Fin 0) => 0)
      (Matrix.of (fun (_ _ : Fin 1) => (C 3 : MvPolynomial (Fin 0) ℝ))) j -
      (2 : ℝ) • 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext a b
    fin_cases a; fin_cases b
    norm_num [Matrix.bernsteinCoeff_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [heq]
  exact Matrix.PosSemidef.one

-- Exact reconstruction feeds the box-bound theorem without identifying
-- the child control net with a canonical coefficient map. The second
-- coordinate is collapsed and the first interval is shifted.
example (P : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℝ))
    (hp : ∀ a b i, (P a b).degreeOf i ≤ ![2, 1] i)
    (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (![2, 7] i) (![4, 7] i))
    (hc : ∀ k, (∀ i, k i ≤ ![2, 1] i) →
      (Matrix.bernsteinSubdivideLeft 0 (1/2)
        (Matrix.bernsteinCoeff ![2, 1] (P.map (boxPullback ![2, 7] ![6, 7]))) k -
          lower).PosSemidef) :
    (P.map (eval x) - lower).PosSemidef := by
  have hrep := Matrix.bernsteinExpansion_subdivideLeft_box hp ![2, 7] ![6, 7] 0 (1/2)
  have hcut : Function.update (![6, 7] : Fin 2 → ℝ) 0 4 = ![4, 7] := by
    ext i
    fin_cases i <;> norm_num [Function.update]
  norm_num only [Matrix.cons_val_zero] at hrep
  rw [hcut] at hrep
  exact Matrix.posSemidef_map_eval_sub_of_bernsteinExpansion_box hrep hx hc

example (P : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℝ))
    (hp : ∀ a b i, (P a b).degreeOf i ≤ ![2, 1] i)
    (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (![4, 7] i) (![6, 7] i))
    (hc : ∀ k, (∀ i, k i ≤ ![2, 1] i) →
      (Matrix.bernsteinSubdivideRight ![2, 1] 0 (1/2)
        (Matrix.bernsteinCoeff ![2, 1] (P.map (boxPullback ![2, 7] ![6, 7]))) k -
          lower).PosSemidef) :
    (P.map (eval x) - lower).PosSemidef := by
  have hrep := Matrix.bernsteinExpansion_subdivideRight_box hp ![2, 7] ![6, 7] 0 (1/2)
  have hcut : Function.update (![2, 7] : Fin 2 → ℝ) 0 4 = ![4, 7] := by
    ext i
    fin_cases i <;> norm_num [Function.update]
  norm_num only [Matrix.cons_val_zero] at hrep
  rw [hcut] at hrep
  exact Matrix.posSemidef_map_eval_sub_of_bernsteinExpansion_box hrep hx hc

#print axioms Matrix.posSemidef_bernsteinCoeff_sub_of_le
#print axioms Matrix.posSemidef_bernsteinSubdivideLeft_sub
#print axioms Matrix.posSemidef_bernsteinSubdivideRight_sub
#print axioms Matrix.posSemidef_map_eval_sub_of_bernsteinExpansion_box
#print axioms Matrix.bernsteinExpansion_subdivideLeft_box
#print axioms Matrix.bernsteinExpansion_subdivideRight_box
