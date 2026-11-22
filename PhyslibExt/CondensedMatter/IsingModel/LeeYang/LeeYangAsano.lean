/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangPolynomial
public import PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangSingleEdge
public import PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangSymmetry

/-!
# The Lee–Yang circle theorem

For the ferromagnetic Ising model on a finite graph, all complex zeros of the partition function
in the fugacity variable lie on the unit circle.

## i. Overview

The proof follows Asano's contraction method. A multi-affine polynomial `p` in variables indexed
by `I` is *polydisc stable* if it has no zero with all variables in the open unit disk. Writing
`p = A + B z_i + C z_j + D z_i z_j` in two of its variables, the *Asano contraction*
`A + D z_i` is again multi-affine and polydisc stable (`asanoContract_stable`).

Give each vertex `v` an anchor variable and each incidence `(v, e)` a half-edge variable. The
product of the factors `1 + z_v` and, for each edge `e = {u, v}`, the edge factor
`1 + w_u w_v + e^{-2β} (w_u + w_v)` is polydisc stable for `β ≥ 0`. Contracting every half-edge
variable into its anchor variable keeps stability, and expanding the result shows that on the
diagonal `z_v = q` it equals `e^{-β |E|}` times the Lee–Yang polynomial evaluated at `q`. Hence
the Lee–Yang polynomial has no zeros in the open unit disk, and by its inversion symmetry none
outside the closed disk.

The coupling is uniform (`J = 1` on every edge) and the inverse temperature satisfies `β ≥ 0`, the
ferromagnetic regime of the theorem. The zeros are those of the polynomial in `z = e^{-2βh}`.

## ii. Key results

- `asanoContract_stable` : Asano's contraction lemma.
- `leeYangComplexPolynomial_ne_zero_in_openUnitDisk` : no zeros with `|q| < 1`.
- `finiteGraph_hasLeeYangCircle` : the Lee–Yang circle theorem.

## iii. Table of contents

- A. Asano contraction
- B. The half-edge polynomial
- C. Contracting all incidences
- D. Expansion of the contracted polynomial
- E. Restriction to the diagonal
- F. The Lee–Yang circle theorem

## iv. References

- T. D. Lee and C. N. Yang, *Statistical theory of equations of state and phase transitions. II.
  Lattice gas and Ising model*, Phys. Rev. 87 (1952) 410–419.
- T. Asano, *Lee–Yang theorem and the Griffiths inequality for the anisotropic Heisenberg
  ferromagnet*, Phys. Rev. Lett. 24 (1970) 1409–1411.
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press (2017), Section 3.7.
-/

@[expose] public section

open scoped ComplexConjugate

namespace StatMech.LeeYang

/-! ## A. Asano contraction -/

/-- Asano's lemma in one variable: if `A + E t + D t²` has no zero in the open unit disk, then
neither has `A + D t`. -/
theorem asano_quadratic_contraction
    (A E D z : ℂ)
    (hstable : ∀ t : ℂ, ‖t‖ < 1 → A + E * t + D * t ^ 2 ≠ 0)
    (hz : ‖z‖ < 1) : A + D * z ≠ 0 := by
  intro hzero
  by_cases hD : D = 0
  · subst D
    have hA : A = 0 := by simpa using hzero
    exact hstable 0 (by simp) (by simp [hA])
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (E ^ 2 - 4 * D * A) (by omega : 0 < 2)
    let x : ℂ := (-E + r) / (2 * D)
    let y : ℂ := (-E - r) / (2 * D)
    have hxroot : A + E * x + D * x ^ 2 = 0 := by
      dsimp only [x]
      field_simp [hD]
      linear_combination hr
    have hyroot : A + E * y + D * y ^ 2 = 0 := by
      dsimp only [y]
      field_simp [hD]
      linear_combination hr
    have hxnorm : 1 ≤ ‖x‖ := by
      exact not_lt.mp (fun hx => hstable x hx hxroot)
    have hynorm : 1 ≤ ‖y‖ := by
      exact not_lt.mp (fun hy => hstable y hy hyroot)
    have hxy : x * y = A / D := by
      dsimp only [x, y]
      field_simp [hD]
      linear_combination -hr
    have hratio : 1 ≤ ‖A / D‖ := by
      rw [← hxy, norm_mul]
      nlinarith [norm_nonneg x, norm_nonneg y]
    have hzratio : z = -(A / D) := by
      apply (mul_left_cancel₀ hD)
      rw [mul_neg, mul_div_cancel₀ A hD]
      exact eq_neg_of_add_eq_zero_right hzero
    rw [hzratio, norm_neg] at hz
    exact (not_lt_of_ge hratio) hz

/-- A function of finitely many complex variables is multi-affine if it is affine in each variable
separately. -/
def IsMultiAffine {I : Type*} [DecidableEq I] (p : (I → ℂ) → ℂ) : Prop :=
  ∀ (i : I) (z : I → ℂ) (t : ℂ),
    p (Function.update z i t) =
      p (Function.update z i 0) +
        t * (p (Function.update z i 1) - p (Function.update z i 0))

/-- A function of complex variables is polydisc stable if it has no zero when every variable lies in
the open unit disk. -/
def PolydiscStable {I : Type*} (p : (I → ℂ) → ℂ) : Prop :=
  ∀ z : I → ℂ, (∀ i, ‖z i‖ < 1) → p z ≠ 0

/-- The Asano contraction of the variables `i` and `j`: for `p = A + B z_i + C z_j + D z_i z_j` it
is `A + D z_i`, computed from the values of `p` at `z_i, z_j ∈ {0, 1}`. -/
def asanoContract {I : Type*} [DecidableEq I]
    (p : (I → ℂ) → ℂ) (i j : I) :
    (I → ℂ) → ℂ := fun z ↦
  let z00 := Function.update (Function.update z i 0) j 0
  let z10 := Function.update (Function.update z i 1) j 0
  let z01 := Function.update (Function.update z i 0) j 1
  let z11 := Function.update (Function.update z i 1) j 1
  p z00 + z i * (p z11 - p z10 - p z01 + p z00)

/-- Asano's contraction lemma: the Asano contraction of a multi-affine polydisc-stable polynomial is
polydisc stable (Asano, Phys. Rev. Lett. 24 (1970)). -/
theorem asanoContract_stable {I : Type*} [DecidableEq I]
    (p : (I → ℂ) → ℂ) (hpAff : IsMultiAffine p)
    (hpStable : PolydiscStable p) {i j : I} (hij : i ≠ j) :
    PolydiscStable (asanoContract p i j) := by
  intro z hz
  let z00 := Function.update (Function.update z i 0) j 0
  let z10 := Function.update (Function.update z i 1) j 0
  let z01 := Function.update (Function.update z i 0) j 1
  let z11 := Function.update (Function.update z i 1) j 1
  let A := p z00
  let E := p z10 + p z01 - 2 * p z00
  let D := p z11 - p z10 - p z01 + p z00
  have hdiag (t : ℂ) :
      p (Function.update (Function.update z i t) j t) =
        A + E * t + D * t ^ 2 := by
    rw [Function.update_comm hij t t z]
    rw [hpAff i (Function.update z j t) t]
    rw [← Function.update_comm hij 0 t z,
      ← Function.update_comm hij 1 t z]
    rw [hpAff j (Function.update z i 0) t,
      hpAff j (Function.update z i 1) t]
    simp only [A, E, D, z00, z10, z01, z11]
    ring
  have hquad : ∀ t : ℂ, ‖t‖ < 1 → A + E * t + D * t ^ 2 ≠ 0 := by
    intro t ht hzero
    apply hpStable (Function.update (Function.update z i t) j t)
    · intro k
      by_cases hki : k = i
      · subst k
        simp [hij, ht]
      · by_cases hkj : k = j
        · subst k
          simp [ht]
        · simp [hki, hkj, hz]
    · rw [hdiag]
      exact hzero
  have hc := asano_quadratic_contraction A E D (z i) hquad (hz i)
  simpa only [asanoContract, A, D, z00, z10, z01, z11, mul_comm] using hc

lemma asanoContract_multiAffine {I : Type*} [DecidableEq I]
    (p : (I → ℂ) → ℂ) (hp : IsMultiAffine p) {i j : I} (hij : i ≠ j) :
    IsMultiAffine (asanoContract p i j) := by
  intro k z t
  by_cases hki : k = i
  · subst k
    simp [asanoContract]
  · by_cases hkj : k = j
    · subst k
      have hcanon (u a b : ℂ) :
          Function.update (Function.update (Function.update z j u) i a) j b =
            Function.update (Function.update z i a) j b := by
        funext x
        by_cases hxj : x = j
        · subst x
          simp
        · by_cases hxi : x = i
          · subst x
            simp [hij]
          · simp [hxj, hxi]
      simp only [asanoContract]
      simp_rw [hcanon]
      simp [hij]
    · have hcomm (a b u : ℂ) :
          Function.update (Function.update (Function.update z k u) i a) j b =
            Function.update (Function.update (Function.update z i a) j b) k u := by
          funext x
          by_cases hxk : x = k
          · subst x
            simp [hki, hkj]
          · by_cases hxi : x = i
            · subst x
              simp [hij, Ne.symm hki]
            · by_cases hxj : x = j
              · subst x
                simp [Ne.symm hkj]
              · simp [hxk, hxi, hxj]
      have hslice (a b u : ℂ) :
          p (Function.update (Function.update (Function.update z k u) i a) j b) =
            p (Function.update
                (Function.update (Function.update z i a) j b) k 0) +
              u * (p (Function.update
                    (Function.update (Function.update z i a) j b) k 1) -
                p (Function.update
                    (Function.update (Function.update z i a) j b) k 0)) := by
        rw [hcomm]
        exact hp k (Function.update (Function.update z i a) j b) u
      simp only [asanoContract]
      rw [hslice 0 0 t, hslice 1 1 t, hslice 1 0 t, hslice 0 1 t]
      rw [hcomm 0 0 0, hcomm 1 1 0, hcomm 1 0 0, hcomm 0 1 0,
        hcomm 0 0 1, hcomm 1 1 1, hcomm 1 0 1, hcomm 0 1 1]
      simp [Ne.symm hki]
      ring

/-- The two-variable edge factor `1 + ab + r (a + b)` with `0 ≤ r ≤ 1` has no zero in the open unit
bidisk. -/
lemma leeYang_edgeFactor_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    1 + a * b + (r : ℂ) * (a + b) ≠ 0 := by
  intro hzero
  have haSq : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hid : Complex.normSq (1 + (r : ℂ) * a) -
      Complex.normSq (a + (r : ℂ)) =
        (1 - r ^ 2) * (1 - Complex.normSq a) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq : Complex.normSq (a + (r : ℂ)) ≤
      Complex.normSq (1 + (r : ℂ) * a) := by
    rw [sub_eq_iff_eq_add] at hid
    rw [hid]
    have hrSqLe : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
    nlinarith
  have hnorm : ‖a + (r : ℂ)‖ ≤ ‖1 + (r : ℂ) * a‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (a + (r : ℂ)), norm_nonneg (1 + (r : ℂ) * a)]
  have hrelation : 1 + (r : ℂ) * a = -(b * (a + (r : ℂ))) := by
    linear_combination hzero
  have hdenom : 0 < ‖a + (r : ℂ)‖ := by
    rw [norm_pos_iff]
    intro hden
    have haeq : a = -(r : ℂ) := by linear_combination hden
    rw [haeq] at hzero
    have hrSq : r ^ 2 = 1 := by
      have hc : (1 : ℂ) - (r : ℂ) ^ 2 = 0 := by
        linear_combination hzero
      have hrreal : 1 - r ^ 2 = 0 := by
        apply Complex.ofReal_eq_zero.mp
        simpa using hc
      nlinarith
    have hrEq : r = 1 := by nlinarith
    subst r
    simp only [Complex.ofReal_one] at haeq
    rw [haeq] at ha
    norm_num at ha
  rw [hrelation, norm_neg, norm_mul] at hnorm
  nlinarith [mul_lt_mul_of_pos_right hb hdenom]

open scoped BigOperators
open StatMech.Ising StatMech.LeeYang StatMech.LeeYang

noncomputable local instance leeYangAsanoPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. The half-edge polynomial -/

/-- The variables of the half-edge polynomial: one anchor variable per vertex and one half-edge
variable per incidence `(v, e)`. -/
abbrev LeeYangVar : Type _ := V ⊕ (V × ↑G.edgeFinset)

/-- The anchor variable of a vertex. -/
def leeYangAnchor (v : V) : LeeYangVar G := Sum.inl v

/-- The half-edge variable of the incidence `(v, e)`. -/
def leeYangHalf (v : V) (e : ↑G.edgeFinset) : LeeYangVar G := Sum.inr (v, e)

/-- The edge factor `1 + w_u w_v + e^{-2β} (w_u + w_v)` of the edge `e = {u, v}`, in its half-edge
variables. -/
noncomputable def leeYangNormalizedEdgeFactor (beta : ℝ)
    (e : ↑G.edgeFinset) (z : LeeYangVar G → ℂ) : ℂ :=
  Sym2.lift ⟨fun u v ↦
    1 + z (leeYangHalf G u e) * z (leeYangHalf G v e) +
      (Real.exp (-2 * beta) : ℂ) *
        (z (leeYangHalf G u e) + z (leeYangHalf G v e)), by
          intro u v
          ring⟩ e.1

/-- The half-edge polynomial: the product of `1 + z_v` over the vertices and of the edge factors
over the edges. -/
noncomputable def leeYangHalfEdgeProduct (beta : ℝ)
    (z : LeeYangVar G → ℂ) : ℂ :=
  (∏ v : V, (1 + z (leeYangAnchor G v))) *
    ∏ e : ↑G.edgeFinset, leeYangNormalizedEdgeFactor G beta e z

/-- The vertex part `∏_v (1 + z_v)` of the half-edge polynomial. -/
noncomputable def leeYangAnchorProduct (z : LeeYangVar G → ℂ) : ℂ :=
  ∏ v : V, (1 + z (leeYangAnchor G v))

/-- The edge part of the half-edge polynomial: the product of the edge factors. -/
noncomputable def leeYangEdgeProduct (beta : ℝ) (z : LeeYangVar G → ℂ) : ℂ :=
  ∏ e : ↑G.edgeFinset, leeYangNormalizedEdgeFactor G beta e z

omit [DecidableEq V] in
lemma leeYangHalfEdgeProduct_eq (beta : ℝ) (z : LeeYangVar G → ℂ) :
    leeYangHalfEdgeProduct G beta z =
      leeYangAnchorProduct G z * leeYangEdgeProduct G beta z := rfl

omit [DecidableEq V] in
lemma leeYangNormalizedEdgeFactor_ne_zero {beta : ℝ} (hbeta : 0 ≤ beta)
    (e : ↑G.edgeFinset) (z : LeeYangVar G → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) :
    leeYangNormalizedEdgeFactor G beta e z ≠ 0 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [leeYangNormalizedEdgeFactor, Sym2.lift_mk]
      apply leeYang_edgeFactor_ne_zero (r := Real.exp (-2 * beta))
      · positivity
      · rw [Real.exp_le_one_iff]
        linarith
      · exact hz _
      · exact hz _

omit [DecidableEq V] in
lemma leeYangHalfEdgeProduct_stable {beta : ℝ} (hbeta : 0 ≤ beta) :
    PolydiscStable (leeYangHalfEdgeProduct G beta) := by
  intro z hz
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun v _ hv ↦ by
      have heq : z (leeYangAnchor G v) = -1 := by linear_combination hv
      have := hz (leeYangAnchor G v)
      rw [heq] at this
      norm_num at this
  · exact Finset.prod_ne_zero_iff.mpr fun e _ ↦
      leeYangNormalizedEdgeFactor_ne_zero G hbeta e z hz

lemma leeYangNormalizedEdgeFactor_affine (beta : ℝ)
    (e : ↑G.edgeFinset) (w : V) (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangNormalizedEdgeFactor G beta e
        (Function.update z (leeYangHalf G w e) t) =
      leeYangNormalizedEdgeFactor G beta e
          (Function.update z (leeYangHalf G w e) 0) +
        t * (leeYangNormalizedEdgeFactor G beta e
            (Function.update z (leeYangHalf G w e) 1) -
          leeYangNormalizedEdgeFactor G beta e
            (Function.update z (leeYangHalf G w e) 0)) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := by
        apply SimpleGraph.Adj.ne
        simpa [SimpleGraph.mem_edgeFinset] using he
      simp only [leeYangNormalizedEdgeFactor, Sym2.lift_mk]
      by_cases hwu : w = u
      · subst w
        have hpair : (u, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) ≠
            (v, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) := by
          intro h
          exact huv (Prod.mk.inj h).1
        simp [leeYangHalf, Ne.symm hpair]
        ring
      · by_cases hwv : w = v
        · subst w
          have hpair : (u, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) ≠
              (v, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) := by
            intro h
            exact huv (Prod.mk.inj h).1
          simp [leeYangHalf, hpair]
          ring
        · have hpairu : (w, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) ≠
              (u, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) := by
            intro h
            exact hwu (Prod.mk.inj h).1
          have hpairv : (w, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) ≠
              (v, (⟨s(u, v), he⟩ : ↑G.edgeFinset)) := by
            intro h
            exact hwv (Prod.mk.inj h).1
          simp [leeYangHalf, Ne.symm hpairu, Ne.symm hpairv]

lemma leeYangNormalizedEdgeFactor_update_other (beta : ℝ)
    {e e' : ↑G.edgeFinset} (hee : e' ≠ e) (w : V)
    (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangNormalizedEdgeFactor G beta e
        (Function.update z (leeYangHalf G w e') t) =
      leeYangNormalizedEdgeFactor G beta e z := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hpairu : (w, e') ≠ (u, ⟨s(u, v), he⟩) := by
        intro h
        apply hee
        exact congrArg Prod.snd h
      have hpairv : (w, e') ≠ (v, ⟨s(u, v), he⟩) := by
        intro h
        apply hee
        exact congrArg Prod.snd h
      simp only [leeYangNormalizedEdgeFactor, Sym2.lift_mk]
      rw [show Function.update z (leeYangHalf G w e') t
          (leeYangHalf G u ⟨s(u, v), he⟩) =
          z (leeYangHalf G u ⟨s(u, v), he⟩) by
            simp [leeYangHalf, Ne.symm hpairu],
        show Function.update z (leeYangHalf G w e') t
          (leeYangHalf G v ⟨s(u, v), he⟩) =
          z (leeYangHalf G v ⟨s(u, v), he⟩) by
            simp [leeYangHalf, Ne.symm hpairv]]

lemma leeYangNormalizedEdgeFactor_update_anchor (beta : ℝ)
    (e : ↑G.edgeFinset) (w : V) (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangNormalizedEdgeFactor G beta e
        (Function.update z (leeYangAnchor G w) t) =
      leeYangNormalizedEdgeFactor G beta e z := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp [leeYangNormalizedEdgeFactor, leeYangHalf, leeYangAnchor]

lemma leeYangAnchorProduct_affine (w : V) (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) t) =
      leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 0) +
        t * (leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 1) -
          leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) 0)) := by
  let R : ℂ := ∏ v ∈ (Finset.univ.erase w), (1 + z (leeYangAnchor G v))
  have hfactor (u : ℂ) :
      leeYangAnchorProduct G (Function.update z (leeYangAnchor G w) u) =
        (1 + u) * R := by
    unfold leeYangAnchorProduct
    rw [← Finset.mul_prod_erase Finset.univ
      (fun v ↦ 1 + Function.update z (leeYangAnchor G w) u (leeYangAnchor G v))
      (Finset.mem_univ w)]
    congr 1
    · simp [leeYangAnchor]
    · apply Finset.prod_congr rfl
      intro v hv
      have hvw : v ≠ w := (Finset.mem_erase.mp hv).1
      simp [leeYangAnchor, hvw]
  rw [hfactor t, hfactor 0, hfactor 1]
  ring

lemma leeYangAnchorProduct_update_half (w : V) (e : ↑G.edgeFinset)
    (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangAnchorProduct G (Function.update z (leeYangHalf G w e) t) =
      leeYangAnchorProduct G z := by
  unfold leeYangAnchorProduct
  apply Finset.prod_congr rfl
  intro v hv
  simp [leeYangAnchor, leeYangHalf]

lemma leeYangEdgeProduct_update_anchor (beta : ℝ) (w : V)
    (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangEdgeProduct G beta (Function.update z (leeYangAnchor G w) t) =
      leeYangEdgeProduct G beta z := by
  unfold leeYangEdgeProduct
  apply Finset.prod_congr rfl
  intro e he
  exact leeYangNormalizedEdgeFactor_update_anchor G beta e w z t

lemma leeYangEdgeProduct_affine (beta : ℝ) (w : V) (e : ↑G.edgeFinset)
    (z : LeeYangVar G → ℂ) (t : ℂ) :
    leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) t) =
      leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 0) +
        t * (leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 1) -
          leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) 0)) := by
  let R : ℂ := ∏ f ∈ (Finset.univ.erase e), leeYangNormalizedEdgeFactor G beta f z
  have hfactor (u : ℂ) :
      leeYangEdgeProduct G beta (Function.update z (leeYangHalf G w e) u) =
        leeYangNormalizedEdgeFactor G beta e
          (Function.update z (leeYangHalf G w e) u) * R := by
    unfold leeYangEdgeProduct
    rw [← Finset.mul_prod_erase Finset.univ
      (fun f ↦ leeYangNormalizedEdgeFactor G beta f
        (Function.update z (leeYangHalf G w e) u)) (Finset.mem_univ e)]
    congr 1
    apply Finset.prod_congr rfl
    intro f hf
    have hfe : e ≠ f := Ne.symm (Finset.mem_erase.mp hf).1
    rw [leeYangNormalizedEdgeFactor_update_other G beta hfe w z u]
  rw [hfactor t, hfactor 0, hfactor 1,
    leeYangNormalizedEdgeFactor_affine G beta e w z t]
  ring

lemma leeYangHalfEdgeProduct_multiAffine (beta : ℝ) :
    IsMultiAffine (leeYangHalfEdgeProduct G beta) := by
  intro k z t
  rcases k with w | ⟨w, e⟩
  · change leeYangHalfEdgeProduct G beta
        (Function.update z (leeYangAnchor G w) t) = _
    simp_rw [leeYangHalfEdgeProduct_eq]
    rw [leeYangAnchorProduct_affine G w z t]
    simp only [leeYangAnchor]
    have hedge (u : ℂ) :
        leeYangEdgeProduct G beta (Function.update z (Sum.inl w) u) =
          leeYangEdgeProduct G beta z := by
      simpa only [leeYangAnchor] using leeYangEdgeProduct_update_anchor G beta w z u
    simp_rw [hedge]
    ring
  · change leeYangHalfEdgeProduct G beta
        (Function.update z (leeYangHalf G w e) t) = _
    simp_rw [leeYangHalfEdgeProduct_eq]
    rw [leeYangEdgeProduct_affine G beta w e z t]
    simp only [leeYangHalf]
    have hanchor (u : ℂ) :
        leeYangAnchorProduct G (Function.update z (Sum.inr (w, e)) u) =
          leeYangAnchorProduct G z := by
      simpa only [leeYangHalf] using leeYangAnchorProduct_update_half G w e z u
    simp_rw [hanchor]
    ring

/-! ## C. Contracting all incidences -/

/-- Successive Asano contraction of the half-edge variable of each incidence in the list into the
anchor variable of its vertex. -/
def leeYangContractList (L : List (V × ↑G.edgeFinset))
    (p : (LeeYangVar G → ℂ) → ℂ) : (LeeYangVar G → ℂ) → ℂ :=
  L.foldl (fun q x ↦ asanoContract q (leeYangAnchor G x.1)
    (leeYangHalf G x.1 x.2)) p

lemma leeYangContractList_multiAffine (L : List (V × ↑G.edgeFinset))
    (p : (LeeYangVar G → ℂ) → ℂ) (hp : IsMultiAffine p) :
    IsMultiAffine (leeYangContractList G L p) := by
  induction L generalizing p with
  | nil => exact hp
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      apply ih
      apply asanoContract_multiAffine p hp
      simp [leeYangAnchor, leeYangHalf]

lemma leeYangContractList_stable (L : List (V × ↑G.edgeFinset))
    (p : (LeeYangVar G → ℂ) → ℂ) (hpAff : IsMultiAffine p)
    (hpStable : PolydiscStable p) :
    PolydiscStable (leeYangContractList G L p) := by
  induction L generalizing p with
  | nil => exact hpStable
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      apply ih
      · apply asanoContract_multiAffine p hpAff
        simp [leeYangAnchor, leeYangHalf]
      · apply asanoContract_stable p hpAff hpStable
        simp [leeYangAnchor, leeYangHalf]

/-- The incidences `(v, e)` of `G`, with `v` an endpoint of `e`. -/
noncomputable def leeYangIncidenceFinset : Finset (V × ↑G.edgeFinset) :=
  Finset.univ.filter fun x ↦ x.1 ∈ x.2.1

/-- The half-edge polynomial after contracting every incidence. -/
noncomputable def leeYangContractedProduct (beta : ℝ) :
    (LeeYangVar G → ℂ) → ℂ :=
  leeYangContractList G (leeYangIncidenceFinset G).toList
    (leeYangHalfEdgeProduct G beta)

lemma leeYangContractedProduct_multiAffine (beta : ℝ) :
    IsMultiAffine (leeYangContractedProduct G beta) :=
  leeYangContractList_multiAffine G _ _ (leeYangHalfEdgeProduct_multiAffine G beta)

lemma leeYangContractedProduct_stable {beta : ℝ} (hbeta : 0 ≤ beta) :
    PolydiscStable (leeYangContractedProduct G beta) :=
  leeYangContractList_stable G _ _ (leeYangHalfEdgeProduct_multiAffine G beta)
    (leeYangHalfEdgeProduct_stable G hbeta)

/-! ## D. Expansion of the contracted polynomial -/

/-- The monomial `∏_{i ∈ S} z_i`. -/
def leeYangMonomial {I : Type*} (S : Finset I) (z : I → ℂ) : ℂ :=
  ∏ i ∈ S, z i

lemma leeYangMonomial_update {I : Type*} [DecidableEq I]
    (S : Finset I) (z : I → ℂ) (i : I) (u : ℂ) :
    leeYangMonomial S (Function.update z i u) =
      if i ∈ S then u * leeYangMonomial (S.erase i) z else leeYangMonomial S z := by
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    unfold leeYangMonomial
    rw [← Finset.mul_prod_erase S (fun k ↦ Function.update z i u k) hi]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro k hk
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [hki]
  · rw [ite_eq_right hi]
    unfold leeYangMonomial
    apply Finset.prod_congr rfl
    intro k hk
    have hki : k ≠ i := fun h ↦ hi (h ▸ hk)
    simp [hki]

lemma asanoContract_add {I : Type*} [DecidableEq I]
    (p q : (I → ℂ) → ℂ) (i j : I) :
    asanoContract (fun z ↦ p z + q z) i j =
      fun z ↦ asanoContract p i j z + asanoContract q i j z := by
  funext z
  simp only [asanoContract]
  ring

lemma asanoContract_sum {I A : Type*} [DecidableEq I]
    (s : Finset A) (p : A → (I → ℂ) → ℂ) (i j : I) :
    asanoContract (fun z ↦ ∑ a ∈ s, p a z) i j =
      fun z ↦ ∑ a ∈ s, asanoContract (p a) i j z := by
  classical
  induction s using Finset.induction with
  | empty =>
      funext z
      simp [asanoContract]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [asanoContract_add, ih]

lemma asanoContract_monomial {I : Type*} [DecidableEq I]
    (S : Finset I) (z : I → ℂ) {i j : I} (hij : i ≠ j) :
    asanoContract (leeYangMonomial S) i j z =
      if (i ∈ S ↔ j ∈ S) then
        leeYangMonomial (S.erase j) z else 0 := by
  unfold asanoContract
  simp_rw [leeYangMonomial_update]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp_all only [ne_eq, ↓reduceIte, Finset.mem_erase, not_false_eq_true, and_self, zero_mul,
      mul_zero, one_mul, sub_zero, add_zero, zero_add]
    unfold leeYangMonomial
    exact Finset.mul_prod_erase (S.erase j) z (Finset.mem_erase.mpr ⟨hij, hi⟩)
  · simp_all
  · simp_all [Finset.mem_erase]
  · simp_all

/-- A chosen first endpoint of an edge. -/
noncomputable def leeYangEndpoint0 (e : ↑G.edgeFinset) : V := e.1.out.1

/-- The other endpoint of an edge. -/
noncomputable def leeYangEndpoint1 (e : ↑G.edgeFinset) : V := e.1.out.2

omit [DecidableEq V] in
lemma leeYang_endpoints_mk (e : ↑G.edgeFinset) :
    s(leeYangEndpoint0 G e, leeYangEndpoint1 G e) = e.1 := by
  change Sym2.mk e.1.out.1 e.1.out.2 = e.1
  rw [Sym2.mk, e.1.out_eq]

omit [DecidableEq V] in
lemma leeYang_endpoints_ne (e : ↑G.edgeFinset) :
    leeYangEndpoint0 G e ≠ leeYangEndpoint1 G e := by
  refine SimpleGraph.Adj.ne (G := G) ?_
  have he : e.1 ∈ G.edgeFinset := e.2
  rw [← leeYang_endpoints_mk G e] at he
  simpa [SimpleGraph.mem_edgeFinset] using he

/-- The term of `1 + z_v` selected by a Boolean choice. -/
def leeYangAnchorChoiceFactor (z : LeeYangVar G → ℂ) (v : V) (b : Bool) : ℂ :=
  if b then z (leeYangAnchor G v) else 1

/-- The term of the edge factor selected by a pair of Boolean choices, one per endpoint. -/
noncomputable def leeYangEdgeChoiceFactor (beta : ℝ) (z : LeeYangVar G → ℂ)
    (e : ↑G.edgeFinset) (b : Bool × Bool) : ℂ :=
  (if b.1 = b.2 then 1 else (Real.exp (-2 * beta) : ℂ)) *
    (if b.1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1) *
    (if b.2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1)

omit [DecidableEq V] in
lemma sum_leeYangAnchorChoiceFactor (z : LeeYangVar G → ℂ) (v : V) :
    ∑ b : Bool, leeYangAnchorChoiceFactor G z v b = 1 + z (leeYangAnchor G v) := by
  simp [leeYangAnchorChoiceFactor, add_comm]

omit [DecidableEq V] in
lemma sum_leeYangEdgeChoiceFactor (beta : ℝ) (z : LeeYangVar G → ℂ)
    (e : ↑G.edgeFinset) :
    ∑ b : Bool × Bool, leeYangEdgeChoiceFactor G beta z e b =
      leeYangNormalizedEdgeFactor G beta e z := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  unfold leeYangEdgeChoiceFactor
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
  have hout := leeYang_endpoints_mk G e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [leeYangNormalizedEdgeFactor, Sym2.lift_mk] at ⊢ hout
      have h0 : leeYangEndpoint0 G ⟨s(u, v), he⟩ = u ∧
          leeYangEndpoint1 G ⟨s(u, v), he⟩ = v ∨
          leeYangEndpoint0 G ⟨s(u, v), he⟩ = v ∧
          leeYangEndpoint1 G ⟨s(u, v), he⟩ = u :=
        Sym2.eq_iff.mp hout
      rcases h0 with h0 | h0 <;> rw [h0.1, h0.2] <;> ring

/-- The term of the expanded half-edge polynomial selected by a choice at every vertex and every
edge. -/
noncomputable def leeYangChoiceTerm (beta : ℝ)
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool))
    (z : LeeYangVar G → ℂ) : ℂ :=
  (∏ v : V, leeYangAnchorChoiceFactor G z v (x.1 v)) *
    ∏ e : ↑G.edgeFinset, leeYangEdgeChoiceFactor G beta z e (x.2 e)

lemma leeYangHalfEdgeProduct_eq_sum_choices (beta : ℝ) :
    leeYangHalfEdgeProduct G beta =
      fun z ↦ ∑ x : (V → Bool) × (↑G.edgeFinset → Bool × Bool),
        leeYangChoiceTerm G beta x z := by
  funext z
  rw [leeYangHalfEdgeProduct_eq]
  unfold leeYangAnchorProduct leeYangEdgeProduct leeYangChoiceTerm
  simp_rw [← sum_leeYangAnchorChoiceFactor G z,
    ← sum_leeYangEdgeChoiceFactor G beta z]
  rw [Fintype.prod_sum, Fintype.prod_sum, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_mul]

/-- The coefficient of a term of the expanded half-edge polynomial: `e^{-2β}` for every edge whose
two choices differ. -/
noncomputable def leeYangChoiceWeight (beta : ℝ)
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)) : ℂ :=
  ∏ e : ↑G.edgeFinset,
    if (x.2 e).1 = (x.2 e).2 then 1 else (Real.exp (-2 * beta) : ℂ)

/-- Whether a choice selects each variable. -/
noncomputable def leeYangChoiceSelected
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)) :
    LeeYangVar G → Bool
  | Sum.inl v => x.1 v
  | Sum.inr (v, e) =>
      if v = leeYangEndpoint0 G e then (x.2 e).1
      else if v = leeYangEndpoint1 G e then (x.2 e).2
      else false

/-- The set of variables selected by a choice, the support of its monomial. -/
noncomputable def leeYangChoiceSupport
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)) :
    Finset (LeeYangVar G) :=
  Finset.univ.filter fun k ↦ leeYangChoiceSelected G x k = true

lemma leeYangChoiceTerm_eq_weight_monomial (beta : ℝ)
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool))
    (z : LeeYangVar G → ℂ) :
    leeYangChoiceTerm G beta x z =
      leeYangChoiceWeight G beta x * leeYangMonomial (leeYangChoiceSupport G x) z := by
  unfold leeYangChoiceTerm leeYangChoiceWeight leeYangMonomial leeYangChoiceSupport
  rw [Finset.prod_filter]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type]
  have hanchor :
      (∏ v : V, if leeYangChoiceSelected G x (Sum.inl v) = true
          then z (Sum.inl v) else 1) =
        ∏ v : V, leeYangAnchorChoiceFactor G z v (x.1 v) := by
    apply Finset.prod_congr rfl
    intro v hv
    cases hx : x.1 v <;> simp [leeYangChoiceSelected, leeYangAnchorChoiceFactor, hx,
      leeYangAnchor]
  rw [hanchor]
  have hhalf (e : ↑G.edgeFinset) :
      (∏ v : V, if leeYangChoiceSelected G x (Sum.inr (v, e)) = true
          then z (Sum.inr (v, e)) else 1) =
        (if (x.2 e).1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1) *
        (if (x.2 e).2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1) := by
    classical
    calc
      (∏ v : V, if leeYangChoiceSelected G x (Sum.inr (v, e)) = true
          then z (Sum.inr (v, e)) else 1) =
          ∏ v : V,
            (if (x.2 e).1 then
                (if leeYangEndpoint0 G e = v then z (Sum.inr (v, e)) else 1) else 1) *
            (if (x.2 e).2 then
                (if leeYangEndpoint1 G e = v then z (Sum.inr (v, e)) else 1) else 1) := by
        apply Finset.prod_congr rfl
        intro v hv
        by_cases hv0 : v = leeYangEndpoint0 G e
        · subst v
          simp [leeYangChoiceSelected, Ne.symm (leeYang_endpoints_ne G e)]
        · by_cases hv1 : v = leeYangEndpoint1 G e
          · subst v
            simp [leeYangChoiceSelected, leeYang_endpoints_ne G e,
              Ne.symm (leeYang_endpoints_ne G e)]
          · have hv0' : leeYangEndpoint0 G e ≠ v := Ne.symm hv0
            have hv1' : leeYangEndpoint1 G e ≠ v := Ne.symm hv1
            simp [leeYangChoiceSelected, hv0, hv1, hv0', hv1']
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        by_cases h0 : (x.2 e).1 = true <;> by_cases h1 : (x.2 e).2 = true <;>
          simp [h0, h1, leeYangHalf]
  rw [Finset.prod_comm]
  simp_rw [hhalf]
  unfold leeYangEdgeChoiceFactor
  have hedgeprod :
      (∏ e : ↑G.edgeFinset,
        ((if (x.2 e).1 = (x.2 e).2 then 1 else (Real.exp (-2 * beta) : ℂ)) *
          (if (x.2 e).1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1)) *
          (if (x.2 e).2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1)) =
        (∏ e : ↑G.edgeFinset,
          if (x.2 e).1 = (x.2 e).2 then 1 else (Real.exp (-2 * beta) : ℂ)) *
        ∏ e : ↑G.edgeFinset,
          (if (x.2 e).1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1) *
          (if (x.2 e).2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1) := by
    calc
      _ = ∏ e : ↑G.edgeFinset,
          (if (x.2 e).1 = (x.2 e).2 then 1 else (Real.exp (-2 * beta) : ℂ)) *
          ((if (x.2 e).1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1) *
          (if (x.2 e).2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1)) := by
            apply Finset.prod_congr rfl
            intro e he
            ring
      _ = _ := Finset.prod_mul_distrib
  rw [hedgeprod]
  ring

lemma asanoContract_const_mul {I : Type*} [DecidableEq I]
    (c : ℂ) (p : (I → ℂ) → ℂ) (i j : I) :
    asanoContract (fun z ↦ c * p z) i j = fun z ↦ c * asanoContract p i j z := by
  funext z
  simp only [asanoContract]
  ring

lemma leeYangContractList_zero (L : List (V × ↑G.edgeFinset)) :
    leeYangContractList G L (fun _ ↦ 0) = fun _ ↦ 0 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      rw [show asanoContract (fun _ : LeeYangVar G → ℂ ↦ 0)
          (leeYangAnchor G x.1) (leeYangHalf G x.1 x.2) = (fun _ ↦ 0) by
        funext z
        simp [asanoContract]]
      exact ih

lemma leeYangContractList_const_mul (L : List (V × ↑G.edgeFinset))
    (c : ℂ) (p : (LeeYangVar G → ℂ) → ℂ) :
    leeYangContractList G L (fun z ↦ c * p z) =
      fun z ↦ c * leeYangContractList G L p z := by
  induction L generalizing p with
  | nil => rfl
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      rw [asanoContract_const_mul]
      exact ih _

/-- Remove from a set of variables the half-edge variables of the listed incidences. -/
def leeYangEraseHalves (L : List (V × ↑G.edgeFinset))
    (S : Finset (LeeYangVar G)) : Finset (LeeYangVar G) :=
  L.foldl (fun T x ↦ T.erase (leeYangHalf G x.1 x.2)) S

/-- A set of variables is consistent with a list of incidences if each listed half-edge variable is
selected exactly when the anchor variable of its vertex is. -/
def LeeYangConsistent (L : List (V × ↑G.edgeFinset))
    (S : Finset (LeeYangVar G)) : Prop :=
  ∀ x ∈ L, leeYangAnchor G x.1 ∈ S ↔ leeYangHalf G x.1 x.2 ∈ S

lemma leeYangContractList_monomial
    (L : List (V × ↑G.edgeFinset)) (hL : L.Nodup)
    (S : Finset (LeeYangVar G)) (z : LeeYangVar G → ℂ) :
    leeYangContractList G L (leeYangMonomial S) z =
      if LeeYangConsistent G L S then
        leeYangMonomial (leeYangEraseHalves G L S) z else 0 := by
  classical
  induction L generalizing S with
  | nil => simp [leeYangContractList, LeeYangConsistent, leeYangEraseHalves]
  | cons x L ih =>
      have hxL : x ∉ L := (List.nodup_cons.mp hL).1
      have hLT : L.Nodup := (List.nodup_cons.mp hL).2
      let i := leeYangAnchor G x.1
      let j := leeYangHalf G x.1 x.2
      have hij : i ≠ j := by simp [i, j, leeYangAnchor, leeYangHalf]
      have htail : LeeYangConsistent G L (S.erase j) ↔
          LeeYangConsistent G L S := by
        unfold LeeYangConsistent
        apply forall_congr'
        intro y
        apply forall_congr'
        intro hy
        have hyx : y ≠ x := by
          intro h
          subst y
          exact hxL hy
        have hanchor : leeYangAnchor G y.1 ≠ j := by
          simp [j, leeYangAnchor, leeYangHalf]
        have hhalf : leeYangHalf G y.1 y.2 ≠ j := by
          simp [j, leeYangHalf, hyx]
        simp [Finset.mem_erase, hanchor, hhalf]
      have hcons : LeeYangConsistent G (x :: L) S ↔
          (i ∈ S ↔ j ∈ S) ∧ LeeYangConsistent G L S := by
        simp only [LeeYangConsistent, List.mem_cons, forall_eq_or_imp]
        rfl
      simp only [leeYangContractList, List.foldl_cons]
      by_cases hx : i ∈ S ↔ j ∈ S
      · have hfirst : asanoContract (leeYangMonomial S) i j =
            leeYangMonomial (S.erase j) := by
          funext w
          simpa [hx] using asanoContract_monomial S w hij
        change leeYangContractList G L
          (asanoContract (leeYangMonomial S) i j) z = _
        rw [hfirst]
        rw [ih hLT (S.erase j)]
        rw [htail]
        simp only [hcons, hx, true_and]
        rfl
      · have hfirst : asanoContract (leeYangMonomial S) i j = fun _ ↦ 0 := by
          funext w
          simpa [hx] using asanoContract_monomial S w hij
        change leeYangContractList G L
          (asanoContract (leeYangMonomial S) i j) z = _
        rw [hfirst]
        rw [leeYangContractList_zero]
        simp [hcons, hx]

lemma leeYangContractList_sum {A : Type*} [Fintype A]
    (L : List (V × ↑G.edgeFinset)) (p : A → (LeeYangVar G → ℂ) → ℂ) :
    leeYangContractList G L (fun z ↦ ∑ a : A, p a z) =
      fun z ↦ ∑ a : A, leeYangContractList G L (p a) z := by
  classical
  induction L generalizing p with
  | nil => rfl
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      rw [show asanoContract (fun z ↦ ∑ a : A, p a z)
          (leeYangAnchor G x.1) (leeYangHalf G x.1 x.2) =
          (fun z ↦ ∑ a : A, asanoContract (p a)
            (leeYangAnchor G x.1) (leeYangHalf G x.1 x.2) z) by
        simpa using asanoContract_sum
          (Finset.univ : Finset A) p (leeYangAnchor G x.1) (leeYangHalf G x.1 x.2)]
      exact ih _

/-- The edge choices induced by a spin configuration: each edge copies the spins of its
endpoints. -/
noncomputable def leeYangTauOf (sigma : V → Bool) :
    ↑G.edgeFinset → Bool × Bool := fun e ↦
  (sigma (leeYangEndpoint0 G e), sigma (leeYangEndpoint1 G e))

@[simp] lemma leeYangAnchor_mem_choiceSupport
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)) (v : V) :
    leeYangAnchor G v ∈ leeYangChoiceSupport G x ↔ x.1 v = true := by
  simp [leeYangChoiceSupport, leeYangChoiceSelected, leeYangAnchor]

@[simp] lemma leeYangHalf0_mem_choiceSupport
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool))
    (e : ↑G.edgeFinset) :
    leeYangHalf G (leeYangEndpoint0 G e) e ∈ leeYangChoiceSupport G x ↔
      (x.2 e).1 = true := by
  simp [leeYangChoiceSupport, leeYangChoiceSelected, leeYangHalf]

@[simp] lemma leeYangHalf1_mem_choiceSupport
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool))
    (e : ↑G.edgeFinset) :
    leeYangHalf G (leeYangEndpoint1 G e) e ∈ leeYangChoiceSupport G x ↔
      (x.2 e).2 = true := by
  simp [leeYangChoiceSupport, leeYangChoiceSelected, leeYangHalf,
    Ne.symm (leeYang_endpoints_ne G e)]

lemma leeYang_incidence_pair_mem (e : ↑G.edgeFinset) (v : V) :
    (v, e) ∈ leeYangIncidenceFinset G ↔ v ∈ e.1 := by
  simp [leeYangIncidenceFinset]

lemma leeYangChoiceSupport_consistent_iff
    (sigma : V → Bool) (tau : ↑G.edgeFinset → Bool × Bool) :
    LeeYangConsistent G (leeYangIncidenceFinset G).toList
        (leeYangChoiceSupport G (sigma, tau)) ↔
      tau = leeYangTauOf G sigma := by
  constructor
  · intro h
    funext e
    apply Prod.ext
    · have hmem : (leeYangEndpoint0 G e, e) ∈
          (leeYangIncidenceFinset G).toList := by
        rw [Finset.mem_toList, leeYang_incidence_pair_mem]
        exact Sym2.out_fst_mem e.1
      have hc := h _ hmem
      simp only [leeYangAnchor_mem_choiceSupport,
        leeYangHalf0_mem_choiceSupport] at hc
      exact Bool.eq_iff_iff.mpr hc.symm
    · have hmem : (leeYangEndpoint1 G e, e) ∈
          (leeYangIncidenceFinset G).toList := by
        rw [Finset.mem_toList, leeYang_incidence_pair_mem]
        exact Sym2.out_snd_mem e.1
      have hc := h _ hmem
      simp only [leeYangAnchor_mem_choiceSupport,
        leeYangHalf1_mem_choiceSupport] at hc
      exact Bool.eq_iff_iff.mpr hc.symm
  · intro htau p hp
    rcases p with ⟨v, e⟩
    rw [Finset.mem_toList, leeYang_incidence_pair_mem] at hp
    rw [htau]
    have hv : v = leeYangEndpoint0 G e ∨ v = leeYangEndpoint1 G e := by
      rw [← leeYang_endpoints_mk G e] at hp
      simpa using hp
    rcases hv with rfl | rfl
    · simp [leeYangTauOf]
    · simp [leeYangTauOf]

lemma mem_leeYangEraseHalves (L : List (V × ↑G.edgeFinset))
    (S : Finset (LeeYangVar G)) (k : LeeYangVar G) :
    k ∈ leeYangEraseHalves G L S ↔
      k ∈ S ∧ ∀ x ∈ L, k ≠ leeYangHalf G x.1 x.2 := by
  induction L generalizing S with
  | nil => simp [leeYangEraseHalves]
  | cons x L ih =>
      simp only [leeYangEraseHalves, List.foldl_cons]
      change k ∈ leeYangEraseHalves G L (S.erase (leeYangHalf G x.1 x.2)) ↔ _
      rw [ih]
      simp only [Finset.mem_erase, List.mem_cons, forall_eq_or_imp]
      aesop

/-- The anchor variables of the vertices with spin `true`. -/
noncomputable def leeYangAnchorSupport (sigma : V → Bool) :
    Finset (LeeYangVar G) :=
  Finset.univ.filter fun k ↦ match k with
    | Sum.inl v => sigma v = true
    | Sum.inr _ => False

lemma leeYangEraseHalves_choiceSupport
    (sigma : V → Bool) (tau : ↑G.edgeFinset → Bool × Bool) :
    leeYangEraseHalves G (leeYangIncidenceFinset G).toList
        (leeYangChoiceSupport G (sigma, tau)) =
      leeYangAnchorSupport G sigma := by
  ext k
  rw [mem_leeYangEraseHalves]
  rcases k with v | ⟨v, e⟩
  · simp [leeYangAnchorSupport, leeYangChoiceSupport, leeYangChoiceSelected,
      leeYangHalf]
  · simp only [leeYangAnchorSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_false]
    intro h
    rcases h with ⟨hsupport, herased⟩
    have hselected : leeYangChoiceSelected G (sigma, tau) (Sum.inr (v, e)) = true := by
      simpa [leeYangChoiceSupport] using hsupport
    have hv : v = leeYangEndpoint0 G e ∨ v = leeYangEndpoint1 G e := by
      unfold leeYangChoiceSelected at hselected
      by_cases h0 : v = leeYangEndpoint0 G e
      · exact Or.inl h0
      · by_cases h1 : v = leeYangEndpoint1 G e
        · exact Or.inr h1
        · simp [h0, h1] at hselected
    apply herased (v, e)
    · rw [Finset.mem_toList, leeYang_incidence_pair_mem]
      rcases hv with rfl | rfl
      · exact Sym2.out_fst_mem e.1
      · exact Sym2.out_snd_mem e.1
    · rfl

lemma leeYangContractedProduct_eq_sum_choices (beta : ℝ)
    (z : LeeYangVar G → ℂ) :
    leeYangContractedProduct G beta z =
      ∑ x : (V → Bool) × (↑G.edgeFinset → Bool × Bool),
        if x.2 = leeYangTauOf G x.1 then
          leeYangChoiceWeight G beta x *
            leeYangMonomial (leeYangAnchorSupport G x.1) z
        else 0 := by
  unfold leeYangContractedProduct
  rw [leeYangHalfEdgeProduct_eq_sum_choices G beta]
  rw [leeYangContractList_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hterm : leeYangChoiceTerm G beta x = fun w ↦
      leeYangChoiceWeight G beta x *
        leeYangMonomial (leeYangChoiceSupport G x) w := by
    funext w
    exact leeYangChoiceTerm_eq_weight_monomial G beta x w
  rw [hterm]
  rw [leeYangContractList_const_mul]
  change leeYangChoiceWeight G beta x *
      leeYangContractList G (leeYangIncidenceFinset G).toList
        (leeYangMonomial (leeYangChoiceSupport G x)) z = _
  rw [leeYangContractList_monomial G _ (Finset.nodup_toList _) _]
  rw [leeYangChoiceSupport_consistent_iff,
    leeYangEraseHalves_choiceSupport]
  by_cases h : x.2 = leeYangTauOf G x.1 <;> simp [h]

lemma leeYangContractedProduct_eq_sum_sigma (beta : ℝ)
    (z : LeeYangVar G → ℂ) :
    leeYangContractedProduct G beta z =
      ∑ sigma : V → Bool,
        leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) *
          leeYangMonomial (leeYangAnchorSupport G sigma) z := by
  rw [leeYangContractedProduct_eq_sum_choices]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [Fintype.sum_eq_single (leeYangTauOf G sigma)]
  · simp
  · simp_all

/-! ## E. Restriction to the diagonal -/

/-- The point with every anchor variable equal to `q` and every half-edge variable equal to `0`. -/
def leeYangDiagonal (q : ℂ) : LeeYangVar G → ℂ
  | Sum.inl _ => q
  | Sum.inr _ => 0

omit [DecidableEq V] in
lemma leeYangMonomial_anchorSupport_diagonal (sigma : V → Bool) (q : ℂ) :
    leeYangMonomial (leeYangAnchorSupport G sigma) (leeYangDiagonal G q) =
      q ^ (Finset.univ.filter fun v ↦ sigma v = true).card := by
  unfold leeYangMonomial leeYangAnchorSupport leeYangDiagonal
  rw [Finset.prod_filter]
  simp only [Fintype.prod_sum_type]
  simp only [Finset.prod_const, one_pow, ite_false, mul_one]
  rw [← Finset.prod_const]
  rw [Finset.prod_filter]

/-- The real weight `∏_e e^{-2β [σ_u ≠ σ_v]}` of a spin configuration. -/
noncomputable def leeYangRealChoiceWeight (beta : ℝ) (sigma : V → Bool) : ℝ :=
  ∏ e : ↑G.edgeFinset,
    if sigma (leeYangEndpoint0 G e) = sigma (leeYangEndpoint1 G e) then 1
    else Real.exp (-2 * beta)

omit [DecidableEq V] in
lemma leeYangChoiceWeight_eq_ofReal (beta : ℝ) (sigma : V → Bool) :
    leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) =
      (leeYangRealChoiceWeight G beta sigma : ℂ) := by
  unfold leeYangChoiceWeight leeYangTauOf leeYangRealChoiceWeight
  push_cast
  apply Finset.prod_congr rfl
  intro e he
  by_cases h : sigma (leeYangEndpoint0 G e) = sigma (leeYangEndpoint1 G e)
  · simp [h]
  · simp [h, Complex.ofReal_exp]

omit [DecidableEq V] in
lemma leeYang_bond_endpoints (sigma : ConfigSpace V) (e : ↑G.edgeFinset) :
    bond sigma e.1 =
      if sigma (leeYangEndpoint0 G e) = sigma (leeYangEndpoint1 G e) then 1 else -1 := by
  rw [← leeYang_endpoints_mk G e, bond_mk]
  unfold spin
  cases h0 : sigma (leeYangEndpoint0 G e) <;>
      cases h1 : sigma (leeYangEndpoint1 G e) <;> simp

omit [DecidableEq V] in
lemma exp_card_mul_leeYangRealChoiceWeight (beta : ℝ) (sigma : ConfigSpace V) :
    Real.exp (beta * G.edgeFinset.card) * leeYangRealChoiceWeight G beta sigma =
      zeroFieldInteractionWeight G beta sigma := by
  have hattach : G.edgeFinset.attach =
      (Finset.univ : Finset (↑G.edgeFinset)) := by
    ext e
    simp
  have hsum : (∑ e ∈ G.edgeFinset, bond sigma e) =
      ∑ e : ↑G.edgeFinset, bond sigma e.1 := by
    rw [← Finset.sum_attach]
    rw [hattach]
  have hexpcard : Real.exp (beta * G.edgeFinset.card) =
      ∏ _e : ↑G.edgeFinset, Real.exp beta := by
    change Real.exp (beta * G.edgeFinset.card) =
      ∏ e ∈ (Finset.univ : Finset (↑G.edgeFinset)), Real.exp beta
    rw [Finset.prod_const, ← Real.exp_nat_mul]
    congr 1
    rw [Finset.card_univ, Fintype.card_coe]
    ring
  unfold zeroFieldInteractionWeight leeYangRealChoiceWeight
  rw [hsum, Finset.mul_sum, Real.exp_sum, hexpcard]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  rw [leeYang_bond_endpoints]
  by_cases h : sigma (leeYangEndpoint0 G e) = sigma (leeYangEndpoint1 G e)
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right h, ← Real.exp_add]
    congr 1
    ring

lemma eval_leeYangComplexPolynomial (beta : ℝ) (q : ℂ) :
    (leeYangComplexPolynomial G beta).eval q =
      ∑ s : ConfigSpace V,
        (zeroFieldInteractionWeight G beta s : ℂ) * q ^ minusSpinCount s := by
  simp [leeYangComplexPolynomial, leeYangPolynomial]

lemma leeYangContractedProduct_diagonal (beta : ℝ) (q : ℂ) :
    (Real.exp (beta * G.edgeFinset.card) : ℂ) *
        leeYangContractedProduct G beta (leeYangDiagonal G q) =
      (leeYangComplexPolynomial G beta).eval q := by
  rw [leeYangContractedProduct_eq_sum_sigma, Finset.mul_sum,
    eval_leeYangComplexPolynomial]
  let F : ConfigSpace V → ℂ := fun sigma ↦
    (Real.exp (beta * G.edgeFinset.card) : ℂ) *
      (leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) *
        leeYangMonomial (leeYangAnchorSupport G sigma) (leeYangDiagonal G q))
  change (∑ sigma : ConfigSpace V, F sigma) = _
  rw [show (∑ sigma : ConfigSpace V, F sigma) =
      ∑ s : ConfigSpace V, F (leeYangFlipEquiv s) by
        simpa using (Equiv.sum_comp leeYangFlipEquiv F).symm]
  apply Finset.sum_congr rfl
  intro s hs
  have hcount :
      (Finset.univ.filter fun v ↦ leeYangFlip s v = true).card =
        minusSpinCount s := by
    unfold minusSpinCount leeYangFlip
    congr 1
  have hweight :
      (Real.exp (beta * G.edgeFinset.card) : ℂ) *
          leeYangChoiceWeight G beta
            (leeYangFlip s, leeYangTauOf G (leeYangFlip s)) =
        (zeroFieldInteractionWeight G beta s : ℂ) := by
    rw [leeYangChoiceWeight_eq_ofReal]
    rw [← Complex.ofReal_mul]
    rw [exp_card_mul_leeYangRealChoiceWeight]
    rw [zeroFieldInteractionWeight_flip]
  simp only [F, leeYangFlipEquiv_apply]
  rw [← mul_assoc, hweight, leeYangMonomial_anchorSupport_diagonal, hcount]

/-! ## F. The Lee–Yang circle theorem -/

/-- The Lee–Yang polynomial of a ferromagnetic Ising model has no zero in the open unit disk. -/
lemma leeYangComplexPolynomial_ne_zero_in_openUnitDisk
    {beta : ℝ} (hbeta : 0 ≤ beta) {q : ℂ} (hq : ‖q‖ < 1) :
    (leeYangComplexPolynomial G beta).eval q ≠ 0 := by
  have hcontracted :
      leeYangContractedProduct G beta (leeYangDiagonal G q) ≠ 0 := by
    apply leeYangContractedProduct_stable G hbeta
    intro k
    rcases k with v | ⟨v, e⟩
    · exact hq
    · simp [leeYangDiagonal]
  intro heval
  have hprod :
      (Real.exp (beta * G.edgeFinset.card) : ℂ) *
          leeYangContractedProduct G beta (leeYangDiagonal G q) = 0 := by
    rw [leeYangContractedProduct_diagonal, heval]
  exact hcontracted ((mul_eq_zero.mp hprod).resolve_left (by
    exact_mod_cast Real.exp_ne_zero (beta * G.edgeFinset.card)))

/-- **Lee–Yang circle theorem.** For the Ising model on a finite graph with uniform ferromagnetic
coupling and `β ≥ 0`, every complex zero of the partition function in the fugacity `z =
e^{-2βh}` lies on the unit circle (Lee and Yang, *Statistical theory of equations of state and
phase transitions. II*, Phys. Rev. 87 (1952)). -/
theorem finiteGraph_hasLeeYangCircle {beta : ℝ} (hbeta : 0 ≤ beta) :
    HasLeeYangCircle G beta := by
  intro z hz
  have hge : 1 ≤ ‖z‖ := by
    exact not_lt.mp (fun hlt ↦
      leeYangComplexPolynomial_ne_zero_in_openUnitDisk G hbeta hlt hz)
  have hle : ‖z‖ ≤ 1 := by
    by_contra h
    have hgt : 1 < ‖z‖ := lt_of_not_ge h
    have hinvnorm : ‖z⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hgt
    have hinvroot : (leeYangComplexPolynomial G beta).eval z⁻¹ = 0 :=
      (leeYangComplexPolynomial_eval_inv_eq_zero_iff' G beta z).2 hz
    exact leeYangComplexPolynomial_ne_zero_in_openUnitDisk G hbeta hinvnorm hinvroot
  exact le_antisymm hle hge

end StatMech.LeeYang
