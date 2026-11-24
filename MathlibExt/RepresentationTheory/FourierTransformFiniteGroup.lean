/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import MathlibExt.GroupTheory.FiniteGroupConvolution

/-!
# Fourier transform on a finite group

The (non-commutative) Fourier transform of a function `P : G → ℂ` on a finite group `G` at a
representation `ρ` is the operator `P̂(ρ) = ∑_s P(s) ρ(s)`. This file records the basic tools of
Diaconis and Shahshahani for random walks on finite groups:

* `conv`, `convPow`: convolution `(P * Q)(s) = ∑_t P(s t⁻¹) Q(t)` and convolution powers;
* `fourier_conv`, `fourier_convPow`: the transform turns convolution into composition;
* `exists_eq_smul_one_of_commute`: Schur's lemma for an operator commuting with an irreducible
  complex representation (a wrapper around Mathlib's
  `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`);
* `fourier_uniform_eq_zero`: the transform of the uniform distribution vanishes at every
  non-trivial irreducible representation;
* `fourier_eq_smul_one_of_isClassFunction`: the transform of a class function at an irreducible
  representation is the scalar `(1 / d_ρ) ∑_s P(s) χ_ρ(s)`.

Sources: P. Diaconis and M. Shahshahani, *Generating a random permutation with random
transpositions*, Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, Section 2; P. Diaconis,
*Applications of non-commutative Fourier analysis to probability problems*, École d'Été de
Probabilités de Saint-Flour XV–XVII, Lecture Notes in Math. 1362 (1988) 51–100, Section 4.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.RepresentationTheory.FourierTransformFiniteGroup

variable {G : Type*} [Group G] [Fintype G]

/-- **Convolution on a finite group.** For functions `P Q : G → R` on a finite group,
`(P * Q)(s) = ∑_t P(s t⁻¹) Q(t)`: to reach `s`, first pick `t` from `Q`, then `s t⁻¹` from `P`
(Diaconis and Shahshahani 1981, Section 2; Diaconis, Saint-Flour notes 1988, Section 4). For a
probability `Q`, the `k`-step law of the random walk driven by `Q` is the convolution power
`convPow Q k`. On complex-valued functions this is the repository's
`MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv` (see `conv_eq_finiteGroupConv`); it is
restated for values in any semiring so that real probabilities (for `tvDist`) can be convolved. -/
def conv {R : Type*} [Semiring R] (P Q : G → R) : G → R :=
  fun s => ∑ t, P (s * t⁻¹) * Q t

/-- **Agreement with the repository's convolution on a finite group.** On complex-valued functions,
`conv P Q` equals `MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv P Q`, written there as
`(P ∗ Q)(x) = ∑_y P(y) Q(y⁻¹ x)`: reindex `t = y⁻¹ x` (Diaconis and Shahshahani 1981, Section 2,
write convolution as `∑_η P(γ η⁻¹) Q(η)`). -/
theorem conv_eq_finiteGroupConv (P Q : G → ℂ) :
    conv P Q = MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv P Q := by
  funext s
  simp only [conv, MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv]
  exact Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft s)) _ _ (fun t => by
    simp [mul_assoc])

/-- **Convolution powers on a finite group.** `convPow Q 0` is the point mass at the identity and
`convPow Q (k + 1) = Q * convPow Q k`, so `convPow Q k` is the law after `k` steps of the random
walk driven by `Q` (Diaconis, Saint-Flour notes 1988, Section 2: `Q^{*k} = Q * Q^{*(k-1)}`). -/
def convPow {R : Type*} [Semiring R] [DecidableEq G] (Q : G → R) : ℕ → G → R
  | 0 => fun s => if s = 1 then 1 else 0
  | k + 1 => conv Q (convPow Q k)

/-- **Total mass of a convolution.** `∑_s (P * Q)(s) = (∑_s P(s)) (∑_s Q(s))`; in particular the
convolution of two probabilities is a probability (Diaconis, Saint-Flour notes 1988, Section 4:
convolution models the composition of two independent random steps). -/
theorem sum_conv {R : Type*} [CommSemiring R] (P Q : G → R) :
    ∑ s, conv P Q s = (∑ s, P s) * ∑ s, Q s := by
  simp only [conv]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_mul]
  exact congrArg (· * Q t) (Equiv.sum_comp (Equiv.mulRight t⁻¹) P)

/-- **Convolution and inversion.** `(P * Q)ˇ = Qˇ * Pˇ`, where `Pˇ(s) = P(s⁻¹)`: reversing a
two-step walk reverses the order of the steps (a direct computation from the definition of
convolution in Diaconis and Shahshahani 1981, Section 2). -/
theorem conv_comp_inv {R : Type*} [CommSemiring R] (P Q : G → R) :
    (fun s => conv P Q s⁻¹) = conv (fun s => Q s⁻¹) (fun s => P s⁻¹) := by
  funext s
  simp only [conv]
  symm
  rw [← Equiv.sum_comp (Equiv.mulRight s)]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.coe_mulRight, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  rw [mul_comm]

/-- **Convolution commutes with ring homomorphisms.** For a ring homomorphism `φ`,
`φ ∘ (P * Q) = (φ ∘ P) * (φ ∘ Q)`, and likewise for convolution powers; used to move a real
probability into `ℂ` before taking Fourier transforms. -/
theorem map_convPow {R S : Type*} [Semiring R] [Semiring S] [DecidableEq G] (φ : R →+* S)
    (Q : G → R) (k : ℕ) (s : G) : φ (convPow Q k s) = convPow (fun t => φ (Q t)) k s := by
  induction k generalizing s with
  | zero => simp only [convPow]; split_ifs <;> simp
  | succ k ih => simp only [convPow, conv, map_sum, map_mul, ih]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Fourier transform at a representation.** For `P : G → ℂ` and a representation `ρ` of `G`
on `V`, `P̂(ρ) = ∑_s P(s) ρ(s)`, an endomorphism of `V` (Diaconis and Shahshahani 1981,
Section 2, where it is written `ρ(P)`; Diaconis, Saint-Flour notes 1988, Section 4). -/
noncomputable def fourier (ρ : Representation ℂ G V) (P : G → ℂ) : Module.End ℂ V :=
  ∑ s, P s • ρ s

/-- **The Fourier transform turns convolution into composition.** For every representation `ρ`,
`(P * Q)^(ρ) = P̂(ρ) Q̂(ρ)` (Diaconis and Shahshahani 1981, Lemma 1). -/
theorem fourier_conv (ρ : Representation ℂ G V) (P Q : G → ℂ) :
    fourier ρ (conv P Q) = fourier ρ P * fourier ρ Q := by
  simp only [fourier, conv, Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulRight t)]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Equiv.coe_mulRight, mul_inv_cancel_right, map_mul, smul_mul_smul_comm, mul_smul]

/-- **Fourier transform of a convolution power.** `(Q^{*k})^(ρ) = Q̂(ρ)^k`: the Fourier transform
reduces the `k`-step law of a random walk to the `k`-th power of one operator (Diaconis and
Shahshahani 1981, Lemma 1 and the remark after Corollary 1). -/
theorem fourier_convPow [DecidableEq G] (ρ : Representation ℂ G V) (Q : G → ℂ) (k : ℕ) :
    fourier ρ (convPow Q k) = fourier ρ Q ^ k := by
  induction k with
  | zero =>
    simp only [fourier, convPow, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, map_one, pow_zero]
  | succ k ih => rw [convPow, fourier_conv, ih, pow_succ']

/-- **Fourier transform of a reversed convolution power.** With `Qˇ(s) = Q(s⁻¹)`,
`((Q^{*k})ˇ)^(ρ) = (Q̂ˇ(ρ))^k`; for a unitary `ρ` the left side is the adjoint of
`(Q^{*k})^(ρ)` when `Q` is real. Follows from `conv_comp_inv` and `fourier_conv`. -/
theorem fourier_convPow_comp_inv [DecidableEq G] (ρ : Representation ℂ G V) (Q : G → ℂ)
    (k : ℕ) : fourier ρ (fun s => convPow Q k s⁻¹) = fourier ρ (fun s => Q s⁻¹) ^ k := by
  induction k with
  | zero =>
    simp only [fourier, convPow, inv_eq_one, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_one, pow_zero]
  | succ k ih =>
    simp only [convPow]
    rw [conv_comp_inv, fourier_conv, ih, pow_succ]

omit [Fintype G] in
/-- **Schur's lemma for an operator commuting with an irreducible representation.** If `ρ` is an
irreducible representation of `G` on a finite-dimensional complex vector space and `A` commutes
with every `ρ(g)`, then `A` is a scalar multiple of the identity (Diaconis and Shahshahani 1981,
Lemma 4, citing Serre, *Linear representations of finite groups*, Section 2.2). This wraps Mathlib's
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`. -/
theorem exists_eq_smul_one_of_commute [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] (A : Module.End ℂ V) (hA : ∀ g, A * ρ g = ρ g * A) :
    ∃ c : ℂ, A = c • 1 := by
  let f : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := A
      isIntertwining' := fun g => hA g }
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 f
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  have hv := congrArg (fun φ : Representation.IntertwiningMap ρ ρ => φ v) hc
  simp only [Algebra.algebraMap_eq_smul_one] at hv
  exact hv.symm.trans (by rfl)

omit [Fintype G] in
/-- **An irreducible representation lives on a nonzero space.** If `ρ` is irreducible then its
underlying space `V` is nontrivial, so `d_ρ = dim V ≥ 1` when `V` is finite-dimensional. This is
built into the definition: Mathlib's `Representation.IsIrreducible` asks the lattice of
subrepresentations to be a simple order, so `0 ≠ V` (compare Diaconis and Shahshahani 1981,
Section 2: `V` admits no invariant subspaces other than `{0}` or `V`). -/
theorem nontrivial_of_isIrreducible (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Nontrivial V := by
  have := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule

/-- **The uniform distribution has zero Fourier transform at non-trivial irreducibles.** If `ρ`
is an irreducible representation of `G` on a finite-dimensional complex vector space and some
`ρ(g)` is not the identity, then the transform of the uniform distribution `U(s) = 1/|G|` at `ρ`
is `0` (Diaconis, Saint-Flour notes 1988, Lemma 4.1). -/
theorem fourier_uniform_eq_zero [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] (hρ : ∃ g, ρ g ≠ 1) :
    fourier ρ (fun _ => ((Fintype.card G : ℂ))⁻¹) = 0 := by
  set S : Module.End ℂ V := ∑ s, ρ s with hS
  have hleft : ∀ h, ρ h * S = S := fun h => by
    rw [hS, Finset.mul_sum]
    simp_rw [← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun s => ρ s)
  have hright : ∀ h, S * ρ h = S := fun h => by
    rw [hS, Finset.sum_mul]
    simp_rw [← map_mul]
    exact Equiv.sum_comp (Equiv.mulRight h) (fun s => ρ s)
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_commute ρ S fun h => by rw [hleft, hright]
  have hc0 : c = 0 := by
    by_contra hne
    obtain ⟨g, hg⟩ := hρ
    apply hg
    have h1 := hleft g
    rw [hc, mul_smul_comm, mul_one] at h1
    exact smul_right_injective _ hne h1
  have : fourier ρ (fun _ => ((Fintype.card G : ℂ))⁻¹) = ((Fintype.card G : ℂ))⁻¹ • S := by
    rw [fourier, hS, Finset.smul_sum]
  rw [this, hc, hc0, zero_smul, smul_zero]

/-- **Fourier transform of a class function at an irreducible representation.** Let `ρ` be an
irreducible representation of `G` on a finite-dimensional complex vector space of dimension
`d_ρ`, with character `χ_ρ`. If `P : G → ℂ` is constant on conjugacy classes, then
`P̂(ρ) = c • 1` with `c = (1 / d_ρ) ∑_s P(s) χ_ρ(s)` (Diaconis and Shahshahani 1981, Lemma 5,
which writes the same sum grouped by conjugacy classes as `(1/d_ρ) ∑_i P_i n_i χ_i`). -/
theorem fourier_eq_smul_one_of_isClassFunction [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (P : G → ℂ)
    (hP : ∀ g h : G, P (h * g * h⁻¹) = P g) :
    fourier ρ P = ((Module.finrank ℂ V : ℂ)⁻¹ * ∑ s, P s * ρ.character s) • 1 := by
  have hcomm : ∀ h, fourier ρ P * ρ h = ρ h * fourier ρ P := fun h => by
    rw [fourier, Finset.sum_mul, Finset.mul_sum]
    rw [← Equiv.sum_comp (MulAut.conj h).toEquiv]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hP,
      smul_mul_assoc, mul_smul_comm, ← map_mul]
    congr 2
    group
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_commute ρ (fourier ρ P) hcomm
  have := nontrivial_of_isIrreducible ρ
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have htr : LinearMap.trace ℂ V (fourier ρ P) = ∑ s, P s * ρ.character s := by
    simp [fourier, map_sum, Representation.character]
  rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul] at htr
  rw [hc, ← htr]
  congr 1
  field_simp

end MathlibExt.RepresentationTheory.FourierTransformFiniteGroup
