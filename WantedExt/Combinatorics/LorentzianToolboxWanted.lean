/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.BivariateLorentzian
public import MathlibExt.Combinatorics.Matroid.IndependenceLorentzian
public import MathlibExt.Combinatorics.Matroid.MConvex
public import WantedExt.Combinatorics.LorentzianPolynomialsWanted
public import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# The Lorentzian toolbox of Brändén and Huh

Basic results of P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020),
821–891 (arXiv:1902.03719v8), stated for the space `L n d` of Lorentzian polynomials of degree
`d` in `n` variables defined in `MathlibExt.Combinatorics.LorentzianPolynomials`
(Definition 2.6 of the paper; by Theorem 2.25 it is the closure of the strictly Lorentzian
polynomials).

* `stable_mem_L`: homogeneous stable polynomials with nonnegative coefficients are Lorentzian
  (Proposition 2.2).
* `mem_L_comp_nonneg`: a nonnegative linear change of variables preserves the Lorentzian
  property (Theorem 2.10).
* `mem_L_directional_derivative`: so do derivatives in nonnegative directions (Corollary 2.11).
* `mem_L_mul`: so do products (the proof of Corollary 2.32).
* `basisGeneratingPolynomial_mem_L`: the basis generating polynomial of a matroid is Lorentzian
  (Theorem 3.10, (8) ⇒ (4)).
* `independenceGeneratingPolynomial_mem_L`: the homogenised generating polynomial of the
  independent sets of a matroid is Lorentzian (the first step of the proof of Theorem 4.14,
  from Theorem 4.10); with Theorem 2.10 and Example 2.26 this gives the strong Mason conjecture.

In each closure statement the transformed polynomial is supplied as an element `g` of the target
space together with an equation for its underlying polynomial, so that no homogeneity proof is
needed in the statement.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LorentzianToolboxWanted

open MvPolynomial Finsupp
open MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials
open MathlibExt.Combinatorics.Matroid.MConvex

/-- **Stable polynomials are Lorentzian** (Brändén and Huh, *Lorentzian polynomials*, Ann. of
Math. 192 (2020), Proposition 2.2). Every homogeneous stable polynomial of degree `d` in `n`
variables with nonnegative coefficients lies in `L n d`. -/
theorem_wanted stable_mem_L {n d : ℕ} (f : H n d) (hf : IsStable f.1)
    (hnn : ∀ m, 0 ≤ f.1.coeff m) : f ∈ L n d

/-- **Nonnegative linear changes of variables preserve Lorentzian polynomials** (Brändén and
Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), Theorem 2.10). If `f(w)` lies in
`L n d` and `A` is an `n × m` matrix with nonnegative entries, then `f(Av)` lies in `L m d`,
where `(Av)_i = ∑_j A i j v_j`. -/
theorem_wanted mem_L_comp_nonneg {n m d : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (f : H n d) (hf : f ∈ L n d) (g : H m d)
    (hg : g.1 = aeval (fun i => ∑ j, A i j • (X j : MvPolynomial (Fin m) ℝ)) f.1) :
    g ∈ L m d

/-- **Directional derivatives in nonnegative directions** (Brändén and Huh, *Lorentzian
polynomials*, Ann. of Math. 192 (2020), Corollary 2.11). If `f` lies in `L n (d + 1)` and
`a_1, …, a_n ≥ 0`, then `∑_i a_i ∂_i f` lies in `L n d`. -/
theorem_wanted mem_L_directional_derivative {n d : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : H n (d + 1)) (hf : f ∈ L n (d + 1)) (g : H n d)
    (hg : g.1 = ∑ i, a i • pderiv i f.1) : g ∈ L n d

/-- **Products of Lorentzian polynomials** (Brändén and Huh, *Lorentzian polynomials*, Ann. of
Math. 192 (2020), proof of Corollary 2.32). If `f` lies in `L n d` and `g` lies in `L n e`,
then `f g` lies in `L n (d + e)`. -/
theorem_wanted mem_L_mul {n d e : ℕ} (f : H n d) (hf : f ∈ L n d) (g : H n e) (hg : g ∈ L n e)
    (h : H n (d + e)) (hh : h.1 = f.1 * g.1) : h ∈ L n (d + e)

open scoped Classical in
/-- **Basis generating polynomials of matroids are Lorentzian** (Brändén and Huh, *Lorentzian
polynomials*, Ann. of Math. 192 (2020), Theorem 3.10, (8) ⇒ (4)). If `M` is a matroid on
`[n]` of rank `d`, then its basis generating polynomial `∑_{B base} ∏_{i ∈ B} w_i` lies in
`L n d`. (For a zero-one set the generating function `f_J = ∑_{α ∈ J} w^α / α!` of the paper is
this polynomial, since `α! = 1`.) -/
theorem_wanted basisGeneratingPolynomial_mem_L {n d : ℕ} (M : _root_.Matroid (Fin n))
    (hd : M.eRank = d) (g : H n d)
    (hg : g.1 = ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => M.IsBase (B : Set (Fin n))),
      monomial (indicatorVec B) (1 : ℝ)) :
    g ∈ L n d

end MathlibExt.Combinatorics.LorentzianToolboxWanted
