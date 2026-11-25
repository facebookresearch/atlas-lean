/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.Bernstein
public import MathlibExt.RingTheory.MvPolynomial.BernsteinElevation
public import MathlibExt.RingTheory.MvPolynomial.BernsteinSubdivision
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Matrix Bernstein refinement preserves fixed matrix bounds

Degree elevation and de Casteljau subdivision combine coefficient matrices
with nonnegative weights summing to one, preserving every fixed matrix lower
bound expressed by a positive-semidefinite difference. The scalar identities
are formalized in the imported elevation and subdivision modules; their source
is A. P. Smith, *Enclosure Methods for Systems of Polynomial Equations and
Inequalities* (2012), §3.3, https://d-nb.info/1028327854/34.
The matrix consequence uses PSD-cone closure as in Boyd and Vandenberghe,
*Convex Optimization*, §2.2.5, https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf.
-/

@[expose] public section

namespace Matrix

open Finset MvPolynomial

variable {ι m r : Type*}

private theorem posSemidef_pair_sub {A B L : Matrix m m ℝ} {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hA : (A - L).PosSemidef) (hB : (B - L).PosSemidef) :
    (u • A + v • B - L).PosSemidef := by
  have h := posSemidef_sum_smul_sub (univ : Finset (Fin 2))
    (w := ![u, v]) (B := ![A, B]) (L := L)
    (by intro i _; fin_cases i <;> assumption)
    (by simpa using huv) (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.sum_univ_two] using h

variable [Fintype ι] [DecidableEq ι]

private theorem posSemidef_bernsteinCoeff_elevate_sub {n : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} {r : ι} {L : Matrix m m ℝ}
    (hp : ∀ a b, (P a b).degreeOf r ≤ n r)
    (hc : ∀ k : ι → ℕ, (∀ i, k i ≤ n i) → (bernsteinCoeff n P k - L).PosSemidef)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ Function.update n r (n r + 1) i) :
    (bernsteinCoeff (Function.update n r (n r + 1)) P k - L).PosSemidef := by
  have hupdate (j : ℕ) (hj : j ≤ n r) : ∀ i, Function.update k r j i ≤ n i := by
    intro i
    by_cases hi : i = r
    · subst i
      simpa using hj
    · simpa [Function.update_of_ne hi] using hk i
  have hkr : k r ≤ n r + 1 := by simpa using hk r
  rcases hj : k r with _ | j
  · have heq : bernsteinCoeff (Function.update n r (n r + 1)) P k =
        bernsteinCoeff n P (Function.update k r 0) := by
      ext a b
      have hu : Function.update k r 0 = k := by simp [← hj]
      simp only [bernsteinCoeff_apply]
      conv_lhs => rw [← hu]
      exact MvPolynomial.bernsteinCoeff_elevate_zero k
    rw [heq]
    exact hc _ (hupdate 0 (Nat.zero_le _))
  · have hu : Function.update k r (j + 1) = k := by simp [← hj]
    have hjn : j ≤ n r := by omega
    by_cases htop : j = n r
    · have heq : bernsteinCoeff (Function.update n r (n r + 1)) P k =
          bernsteinCoeff n P (Function.update k r (n r)) := by
        ext a b
        simp only [bernsteinCoeff_apply]
        conv_lhs => rw [← hu, htop]
        exact MvPolynomial.bernsteinCoeff_elevate_top k (hp a b)
      rw [heq]
      exact hc _ (hupdate _ le_rfl)
    · have hj1 : j + 1 ≤ n r := by omega
      have hweights : ((j + 1 : ℕ) : ℝ) / (n r + 1) +
          ((n r - j : ℕ) : ℝ) / (n r + 1) = 1 := by
        have hpos : (0 : ℝ) < n r + 1 := by positivity
        rw [← add_div, Nat.cast_sub hjn]
        push_cast
        field_simp
        ring
      have heq : bernsteinCoeff (Function.update n r (n r + 1)) P k =
          (((j + 1 : ℕ) : ℝ) / (n r + 1)) • bernsteinCoeff n P (Function.update k r j) +
          (((n r - j : ℕ) : ℝ) / (n r + 1)) •
            bernsteinCoeff n P (Function.update k r (j + 1)) := by
        ext a b
        simp only [bernsteinCoeff_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        conv_lhs => rw [← hu]
        exact MvPolynomial.bernsteinCoeff_elevate_succ k j (hp a b) hjn
      rw [heq]
      exact posSemidef_pair_sub (by positivity) (by positivity) hweights
        (hc _ (hupdate j hjn)) (hc _ (hupdate (j + 1) hj1))

omit [DecidableEq ι] in
/-- Let every entry of a real polynomial matrix have coordinate degrees
bounded by `n`, and let `d i ≥ n i` in every coordinate. If all valid degree-`n`
coefficient matrices exceed a fixed matrix `L` by a positive-semidefinite
difference, the same holds for all valid degree-`d` coefficients. Degrees
may be heterogeneous or zero, and the variable type may be empty. -/
theorem posSemidef_bernsteinCoeff_sub_of_le {n d : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} {L : Matrix m m ℝ}
    (hp : ∀ a b i, (P a b).degreeOf i ≤ n i) (hnd : ∀ i, n i ≤ d i)
    (hc : ∀ k : ι → ℕ, (∀ i, k i ≤ n i) → (bernsteinCoeff n P k - L).PosSemidef)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ d i) : (bernsteinCoeff d P k - L).PosSemidef := by
  classical
  generalize hs : ∑ i, d i = s
  induction s using Nat.strong_induction_on generalizing d k with
  | ind s ih =>
    by_cases heq : n = d
    · subst d
      exact hc k hk
    · obtain ⟨r, hr⟩ : ∃ r, n r < d r := by
        by_contra! h
        exact heq (funext fun i => Nat.le_antisymm (hnd i) (h i))
      let d' := Function.update d r (d r - 1)
      have hn' : ∀ i, n i ≤ d' i := by
        intro i
        by_cases hi : i = r
        · subst i
          simp only [d', Function.update_self]
          omega
        · simpa [d', Function.update_of_ne hi] using hnd i
      have hd' : ∀ i, d' i ≤ d i := by
        intro i
        by_cases hi : i = r
        · subst i
          simp [d']
        · simp [d', Function.update_of_ne hi]
      have hsum : ∑ i, d' i < s := by
        rw [← hs]
        apply sum_lt_sum (fun i _ => hd' i)
        exact ⟨r, mem_univ r, by simp only [d', Function.update_self]; omega⟩
      have hrecover : Function.update d' r (d' r + 1) = d := by
        have hrpos : 0 < d r := by omega
        simp [d', Nat.sub_add_cancel hrpos]
      rw [← hrecover]
      exact posSemidef_bernsteinCoeff_elevate_sub
        (fun a b => (hp a b r).trans (hn' r))
        (fun l hl => ih (∑ i, d' i) hsum hn' l hl rfl) k (by simpa [hrecover] using hk)

/-- The matrix polynomial reconstructed entrywise from a finite tensor
Bernstein control net. Values outside `k i ≤ n i` have no effect. -/
noncomputable def bernsteinExpansion (n : ι → ℕ) (c : (ι → ℕ) → Matrix m r ℝ) :
    Matrix m r (MvPolynomial ι ℝ) :=
  fun a b => MvPolynomial.bernsteinExpansion n (fun k => c k a b)

/-- Left child of a matrix control net under a de Casteljau cut in coordinate
`r`. It is computed entrywise and is not asserted to be a canonical
coefficient map of a child polynomial. -/
noncomputable def bernsteinSubdivideLeft (r : ι) (t : ℝ)
    (c : (ι → ℕ) → Matrix m m ℝ) (k : ι → ℕ) : Matrix m m ℝ :=
  fun a b => MvPolynomial.bernsteinSubdivideLeft r t (fun j => c j a b) k

/-- Right child of a degree-`n` matrix control net under a de Casteljau cut
in coordinate `r`. It is computed entrywise, with depth `n r - k r` at a
valid index; no canonical-coefficient identification is asserted. -/
noncomputable def bernsteinSubdivideRight (n : ι → ℕ) (r : ι) (t : ℝ)
    (c : (ι → ℕ) → Matrix m m ℝ) (k : ι → ℕ) : Matrix m m ℝ :=
  fun a b => MvPolynomial.bernsteinSubdivideRight n r t (fun j => c j a b) k

omit [Fintype ι] [DecidableEq ι] in
private theorem posSemidef_deCasteljau_sub {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    {c : ℕ → Matrix m m ℝ} {L : Matrix m m ℝ} {n : ℕ}
    (hc : ∀ j ≤ n, (c j - L).PosSemidef) :
    (Matrix.of (fun a b => bernsteinPolynomial.deCasteljau t (fun j => c j a b) n) -
      L).PosSemidef := by
  induction n generalizing c with
  | zero =>
    change (c 0 - L).PosSemidef
    exact hc 0 le_rfl
  | succ n ih =>
    have hleft := ih (c := c) (fun j hj => hc j (by omega))
    have hright := ih (c := fun j => c (j + 1)) (fun j hj => hc (j + 1) (by omega))
    convert posSemidef_pair_sub (sub_nonneg.mpr ht.2) ht.1 (by ring) hleft hright using 1
    ext a b
    simp only [bernsteinPolynomial.deCasteljau, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]

omit [Fintype ι] in
/-- At a cut parameter in `[0,1]`, every valid left-child matrix coefficient
preserves any fixed subtraction-PSD lower bound on the valid parent net.
Endpoint cuts and zero coordinate degrees are included. -/
theorem posSemidef_bernsteinSubdivideLeft_sub {n : ι → ℕ} {r : ι} {t : ℝ}
    {c : (ι → ℕ) → Matrix m m ℝ} {L : Matrix m m ℝ} (ht : t ∈ Set.Icc 0 1)
    (hc : ∀ k, (∀ i, k i ≤ n i) → (c k - L).PosSemidef)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n i) :
    (bernsteinSubdivideLeft r t c k - L).PosSemidef := by
  apply posSemidef_deCasteljau_sub ht
  intro j hj
  apply hc
  intro i
  by_cases hi : i = r
  · subst i
    simp only [Function.update_self]
    exact hj.trans (hk r)
  · simpa [Function.update_of_ne hi] using hk i

omit [Fintype ι] in
/-- At a cut parameter in `[0,1]`, every valid right-child matrix coefficient
preserves any fixed subtraction-PSD lower bound on the valid parent net.
Endpoint cuts and zero coordinate degrees are included. -/
theorem posSemidef_bernsteinSubdivideRight_sub {n : ι → ℕ} {r : ι} {t : ℝ}
    {c : (ι → ℕ) → Matrix m m ℝ} {L : Matrix m m ℝ} (ht : t ∈ Set.Icc 0 1)
    (hc : ∀ k, (∀ i, k i ≤ n i) → (c k - L).PosSemidef)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ n i) :
    (bernsteinSubdivideRight n r t c k - L).PosSemidef := by
  apply posSemidef_deCasteljau_sub ht
  intro j hj
  apply hc
  intro i
  by_cases hi : i = r
  · subst i
    simp only [Function.update_self]
    have := hk r
    omega
  · simpa [Function.update_of_ne hi] using hk i

/-- Evaluating a matrix Bernstein control-net expansion is its weighted
sum of coefficient matrices, for every real evaluation point. -/
theorem map_eval_bernsteinExpansion (n : ι → ℕ) (c : (ι → ℕ) → Matrix m r ℝ)
    (x : ι → ℝ) :
    (bernsteinExpansion n c).map (eval x) =
      ∑ k : (i : ι) → Fin (n i + 1),
        eval x (MvPolynomial.bernstein n (fun i => k i)) • c (fun i => k i) := by
  ext a b
  simp only [Matrix.map_apply, bernsteinExpansion, MvPolynomial.bernsteinExpansion,
    map_sum, map_mul, eval_C, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- A fixed subtraction-PSD lower bound on a matrix control net is a lower
bound for its tensor Bernstein expansion throughout the closed unit cube.
The net need not be the canonical coefficients of a polynomial. -/
theorem posSemidef_map_eval_bernsteinExpansion_sub {n : ι → ℕ}
    {c : (ι → ℕ) → Matrix m m ℝ} {L : Matrix m m ℝ} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc 0 1)
    (hc : ∀ k, (∀ i, k i ≤ n i) → (c k - L).PosSemidef) :
    ((bernsteinExpansion n c).map (eval x) - L).PosSemidef := by
  rw [map_eval_bernsteinExpansion]
  exact posSemidef_sum_smul_sub univ (fun k _ => eval_bernstein_nonneg _ _ hx)
    (sum_eval_bernstein n x) (fun k _ => hc _ (fun i => Nat.le_of_lt_succ (k i).isLt))


/-- If a matrix control net reconstructs the affine pullback of a polynomial
matrix to a closed box, any fixed subtraction-PSD bound on its valid entries
holds at every point in that box. The net need not be canonical. Membership
supplies ordered endpoints, including collapsed coordinates. -/
theorem posSemidef_map_eval_sub_of_bernsteinExpansion_box {n : ι → ℕ}
    {c : (ι → ℕ) → Matrix m m ℝ} {P : Matrix m m (MvPolynomial ι ℝ)}
    {a b x : ι → ℝ} {L : Matrix m m ℝ}
    (hrep : bernsteinExpansion n c = P.map (boxPullback a b))
    (hx : ∀ i, x i ∈ Set.Icc (a i) (b i))
    (hc : ∀ k, (∀ i, k i ≤ n i) → (c k - L).PosSemidef) :
    (P.map (eval x) - L).PosSemidef := by
  have hparam (i : ι) : ∃ t ∈ Set.Icc (0 : ℝ) 1, a i + (b i - a i) * t = x i := by
    obtain ⟨u, v, hu, hv, huv, heq⟩ := (Convex.mem_Icc ((hx i).1.trans (hx i).2)).mp (hx i)
    refine ⟨v, ⟨hv, by linarith⟩, ?_⟩
    rw [show u = 1 - v by linarith] at heq
    nlinarith [heq]
  choose t ht heq using hparam
  have h := posSemidef_map_eval_bernsteinExpansion_sub ht hc
  rw [hrep] at h
  have hmap : (P.map (boxPullback a b)).map (eval t) = P.map (eval x) := by
    ext u v
    change eval t (boxPullback a b (P u v)) = eval x (P u v)
    simp only [eval_boxPullback, heq]
  rwa [hmap] at h

/-- The left child of the entrywise canonical coefficient net of a box
pullback reconstructs exactly the left child box pullback of the matrix
polynomial. Every entry satisfies the common coordinate-degree bound.
The algebraic identity allows arbitrary real endpoints and cut parameters,
including zero widths; no canonical-child-coefficient equality is claimed. -/
theorem bernsteinExpansion_subdivideLeft_box {n : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} (hp : ∀ a b i, (P a b).degreeOf i ≤ n i)
    (a b : ι → ℝ) (r : ι) (t : ℝ) :
    bernsteinExpansion n (bernsteinSubdivideLeft r t (bernsteinCoeff n (P.map (boxPullback a b)))) =
      P.map (boxPullback a (Function.update b r ((1 - t) * a r + t * b r))) := by
  apply Matrix.ext
  intro u v
  exact MvPolynomial.bernsteinExpansion_subdivideLeft_box (hp u v) a b r t

/-- The right child of the entrywise canonical coefficient net of a box
pullback reconstructs exactly the right child box pullback of the matrix
polynomial. Every entry satisfies the common coordinate-degree bound.
Arbitrary real endpoints and cuts, including zero widths, are allowed;
no canonical-child-coefficient equality is claimed. -/
theorem bernsteinExpansion_subdivideRight_box {n : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} (hp : ∀ a b i, (P a b).degreeOf i ≤ n i)
    (a b : ι → ℝ) (r : ι) (t : ℝ) :
    bernsteinExpansion n
        (bernsteinSubdivideRight n r t (bernsteinCoeff n (P.map (boxPullback a b)))) =
      P.map (boxPullback (Function.update a r ((1 - t) * a r + t * b r)) b) := by
  apply Matrix.ext
  intro u v
  exact MvPolynomial.bernsteinExpansion_subdivideRight_box (hp u v) a b r t

end Matrix
