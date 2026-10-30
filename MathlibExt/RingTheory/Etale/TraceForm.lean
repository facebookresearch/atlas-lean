/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

/-!
# Trace form, discriminant, and étaleness

For a finite-dimensional commutative algebra `R` over a field `K`, the trace
pairing `⟨x, y⟩ = Tr_{R / K}(x * y)` is nondegenerate if and only if `R` is
étale over `K`. As a consequence, for any `K`-basis `b` of `R` the
discriminant `disc(b)` is nonzero if and only if `R` is étale over `K`.

This is ATLAS `NumberTheoryI` Theorem 5.20 (trace pairing is perfect iff the
algebra is finite étale) and Lemma 12.18 (finite étale iff the discriminant of
a basis is nonzero). In v1, Lemma 12.18 is recorded with the general-algebra
trace-form/étaleness identification taken as an explicit hypothesis
(`thm_5_20`), and Theorem 5.20 itself is proved in v1 only for field
extensions (via Mathlib's separable-field trace-form results). Here the
general-algebra iff is proved: the étale direction uses the classification of
étale algebras as finite products of finite separable field extensions, and
the converse uses nondegeneracy to show that every nilpotent is zero. The
resulting reduced Artinian algebra is a product of fields, each separable
because its trace form is nondegenerate.

## Main results

* `Algebra.trace_pi`: the trace on a finite product of algebras is the sum of
  the traces.
* `Algebra.traceForm_pi`: the trace form on a finite product of algebras is
  the sum of the trace forms.
* `Algebra.traceForm_nondegenerate_iff_etale`: Theorem 5.20.
* `Algebra.discr_ne_zero_iff_etale`: Lemma 12.18.
* `Algebra.discr_ne_zero_of_etale`, `Algebra.etale_of_discr_ne_zero`: the two
  directions of Lemma 12.18.
-/

namespace Algebra

universe u

variable {K : Type u} [Field K]

/-- The trace on a finite product of algebras is the sum of the traces. -/
theorem trace_pi {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, Module.Finite K (A i)] [∀ i, Module.Free K (A i)]
    (x : ∀ i, A i) :
    trace K (∀ i, A i) x = ∑ i, trace K (A i) (x i) := by
  classical
  have hdiag : ∀ (i : ι) (j : Module.Free.ChooseBasisIndex K (A i)),
      (leftMulMatrix (Pi.basis (fun i => Module.Free.chooseBasis K (A i))) x)
        ⟨i, j⟩ ⟨i, j⟩
        = (leftMulMatrix (Module.Free.chooseBasis K (A i)) (x i)) j j := by
    intro i j
    rw [leftMulMatrix_eq_repr_mul, leftMulMatrix_eq_repr_mul, Pi.basis_apply,
      Pi.basis_repr]
    congr 1
    simp [Pi.mul_apply]
  calc trace K (∀ i, A i) x
      = Matrix.trace
          (leftMulMatrix (Pi.basis (fun i => Module.Free.chooseBasis K (A i))) x) :=
        trace_eq_matrix_trace _ x
    _ = ∑ a, (leftMulMatrix (Pi.basis (fun i => Module.Free.chooseBasis K (A i))) x)
        a a := by
        simp only [Matrix.trace, Matrix.diag_apply]
    _ = ∑ i, ∑ j, (leftMulMatrix (Module.Free.chooseBasis K (A i)) (x i)) j j := by
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => hdiag i j
    _ = ∑ i, trace K (A i) (x i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [trace_eq_matrix_trace (Module.Free.chooseBasis K (A i)) (x i)]
        simp only [Matrix.trace, Matrix.diag_apply]

/-- The trace form on a finite product of algebras is the sum of the trace
forms. -/
theorem traceForm_pi {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, Module.Finite K (A i)] [∀ i, Module.Free K (A i)]
    (x y : ∀ i, A i) :
    traceForm K (∀ i, A i) x y
      = ∑ i, traceForm K (A i) (x i) (y i) := by
  rw [traceForm_apply, trace_pi]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.mul_apply, traceForm_apply]

/-- The trace form is unchanged under an algebra equivalence. -/
theorem traceForm_apply_of_algEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (e : R ≃ₐ[K] S) (x y : R) :
    traceForm K S (e x) (e y) = traceForm K R x y := by
  rw [traceForm_apply, traceForm_apply, ← map_mul, trace_eq_of_algEquiv]

/-- A nilpotent element pairs to zero against everything under the trace
form: multiplication by a nilpotent is a nilpotent endomorphism, whose trace
vanishes. -/
theorem traceForm_apply_eq_zero_of_isNilpotent {R : Type*} [CommRing R]
    [Algebra K R] {x y : R} (hx : IsNilpotent x) :
    traceForm K R x y = 0 := by
  rw [traceForm_apply, trace_apply]
  have hxy : IsNilpotent (x * y) := (Commute.all x y).isNilpotent_mul_right hx
  obtain ⟨n, hn⟩ := hxy
  have hnil : IsNilpotent (lmul K R (x * y)) := by
    refine ⟨n, ?_⟩
    rw [← map_pow, hn, map_zero]
  exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero

/-- If the trace form is nondegenerate then the algebra is reduced: every
nilpotent element lies in the kernel of the trace form, hence is zero. -/
theorem isReduced_of_traceForm_nondegenerate {R : Type*} [CommRing R]
    [Algebra K R] (h : (traceForm K R).Nondegenerate) : IsReduced R :=
  ⟨fun x hx => h.1 x fun _ => traceForm_apply_eq_zero_of_isNilpotent hx⟩

/-- ATLAS `NumberTheoryI` Theorem 5.20: for a finite-dimensional commutative
algebra over a field, the trace pairing is nondegenerate if and only if the
algebra is étale. -/
theorem traceForm_nondegenerate_iff_etale {R : Type u} [CommRing R] [Algebra K R]
    [Module.Finite K R] :
    (traceForm K R).Nondegenerate ↔ Etale K R := by
  constructor
  · intro h
    have : IsReduced R := isReduced_of_traceForm_nondegenerate h
    have : IsArtinianRing R := IsArtinianRing.of_finite K R
    classical
    have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
    let e : R ≃ₐ[K] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal :=
      (IsArtinianRing.equivPi R).restrictScalars K
    have hfac : ∀ m : MaximalSpectrum R,
        (traceForm K (R ⧸ m.asIdeal)).Nondegenerate := by
      intro m
      apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
        (LinearMap.BilinForm.IsSymm.isRefl
          (Algebra.traceForm_isSymm (R := K) (S := R ⧸ m.asIdeal)))).mpr
      intro y hy
      have hx : e.symm (Pi.single m y) = 0 := by
        apply h.1
        intro w
        have h1 := traceForm_apply_of_algEquiv e (e.symm (Pi.single m y)) w
        rw [AlgEquiv.apply_symm_apply] at h1
        rw [← h1, traceForm_pi]
        have hsum : ∑ i : MaximalSpectrum R,
              traceForm K (R ⧸ i.asIdeal)
                ((Pi.single (M := fun m : MaximalSpectrum R => R ⧸ m.asIdeal) m y) i)
                ((e w) i)
            = traceForm K (R ⧸ m.asIdeal) y (e w m) := by
          rw [Finset.sum_eq_single m]
          · rw [Pi.single_eq_same]
          · intro i _ hi
            rw [Pi.single_eq_of_ne hi]
            simp
          · intro hmem
            exact absurd (Finset.mem_univ m) hmem
        rw [hsum]
        exact hy (e w m)
      have h2 : Pi.single m y
          = (0 : ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal) := by
        rw [← e.apply_symm_apply (Pi.single m y), hx, map_zero]
      have h3 := congrFun h2 m
      rwa [Pi.single_eq_same] at h3
    have hsep : ∀ m : MaximalSpectrum R,
        Algebra.IsSeparable K (R ⧸ m.asIdeal) := fun m => by
      let _ : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
      exact ((traceForm_nondegenerate_tfae K (R ⧸ m.asIdeal)).out 3 1).mp (hfac m)
    rw [Etale.iff_exists_algEquiv_prod K R]
    exact ⟨MaximalSpectrum R, inferInstance, fun m => R ⧸ m.asIdeal,
      fun m => Ideal.Quotient.field m.asIdeal, fun m => inferInstance, e,
      fun m => ⟨inferInstance, hsep m⟩⟩
  · intro h
    obtain ⟨I, _, A, _, _, e, hA⟩ := (Etale.iff_exists_algEquiv_prod K R).mp h
    classical
    have : Fintype I := Fintype.ofFinite I
    have : ∀ i, Module.Finite K (A i) := fun i => (hA i).1
    have : ∀ i, Module.Free K (A i) := fun _ => inferInstance
    apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (LinearMap.BilinForm.IsSymm.isRefl
        (Algebra.traceForm_isSymm (R := K) (S := R)))).mpr
    intro x hx
    have hex : e x = 0 := by
      apply funext
      intro j
      have : FiniteDimensional K (A j) := (hA j).1
      have : Algebra.IsSeparable K (A j) := (hA j).2
      have hBj : (traceForm K (A j)).Nondegenerate :=
        traceForm_nondegenerate K (A j)
      apply hBj.1
      intro z
      have h1 := hx (e.symm (Pi.single j z))
      rw [← traceForm_apply_of_algEquiv e x (e.symm (Pi.single j z)),
        AlgEquiv.apply_symm_apply] at h1
      rw [traceForm_pi] at h1
      have hsum : ∑ i : I,
            traceForm K (A i) ((e x) i)
              ((Pi.single (M := fun i : I => A i) j z) i)
          = traceForm K (A j) ((e x) j) z := by
        rw [Finset.sum_eq_single j]
        · rw [Pi.single_eq_same]
        · intro i _ hi
          rw [Pi.single_eq_of_ne hi]
          simp
        · intro hmem
          exact absurd (Finset.mem_univ j) hmem
      rw [hsum] at h1
      exact h1
    have hx0 : x = e.symm (e x) := (e.symm_apply_apply x).symm
    rw [hex, map_zero] at hx0
    exact hx0

/-- The discriminant of a basis is nonzero if and only if the trace form is
nondegenerate. -/
theorem discr_ne_zero_iff_traceForm_nondegenerate {R : Type*} [CommRing R]
    [Algebra K R] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K R) :
    Algebra.discr K b ≠ 0 ↔ (traceForm K R).Nondegenerate := by
  rw [Algebra.discr_def, Algebra.traceMatrix_of_basis]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).symm

/-- ATLAS `NumberTheoryI` Lemma 12.18: for a basis of a finite-dimensional
commutative algebra over a field, the discriminant of the basis is nonzero if
and only if the algebra is étale. -/
theorem discr_ne_zero_iff_etale {R : Type u} [CommRing R] [Algebra K R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K R) :
    Algebra.discr K b ≠ 0 ↔ Etale K R := by
  let : Module.Finite K R := Module.Finite.of_basis b
  rw [discr_ne_zero_iff_traceForm_nondegenerate b, traceForm_nondegenerate_iff_etale]

/-- One direction of Lemma 12.18: an étale algebra has nonzero discriminant
for every basis. -/
theorem discr_ne_zero_of_etale {R : Type u} [CommRing R] [Algebra K R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K R)
    (hR : Etale K R) :
    Algebra.discr K b ≠ 0 :=
  (discr_ne_zero_iff_etale b).mpr hR

/-- One direction of Lemma 12.18: a nonzero discriminant for some basis forces
the algebra to be étale. -/
theorem etale_of_discr_ne_zero {R : Type u} [CommRing R] [Algebra K R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K R)
    (h : Algebra.discr K b ≠ 0) :
    Etale K R :=
  (discr_ne_zero_iff_etale b).mp h

end Algebra
