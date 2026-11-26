/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.LogPairs

/-!
# Canonical divisor independence of frames

The canonical divisor of `CanonicalData` on a normal variety depends only on the rational top
form: two canonical data with the same form have the same canonical divisor, since frames change
by local units, which have order zero.

References: Hartshorne, *Algebraic Geometry*, II.6; Kollár--Mori,
*Birational Geometry of Algebraic Varieties*, §2.3.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted

open MathlibExt.AlgebraicGeometry.LogPairs

universe u

private theorem basis_single_smul (R M : Type u) [Semiring R] [AddCommMonoid M] [Module R M]
    (b : Module.Basis Unit R M) (x : M) : (b.repr x ()) • b () = x := by
  have h := b.sum_repr x
  rwa [Fintype.sum_unique] at h

private theorem ord_repr_eq_of_form_eq (k : Type u) [Field k] (n : ℕ) (V : NormalVariety k n)
    (p : PrimePoint V) (eta : RationalTopForms V) (hne : eta ≠ 0)
    (FC FD : CanonicalFrame V p) :
    V.X.left.ord (FC.rationalBasis.repr eta ()) p.val =
      V.X.left.ord (FD.rationalBasis.repr eta ()) p.val := by
  let : Algebra k (LocalRing V p.val) := localAlgebra V p.val
  let : Algebra k (FunctionField V) := fractionAlgebra V
  set a : LocalRing V p.val := FD.localBasis.repr (FC.localBasis ()) ()
  set c : LocalRing V p.val := FC.localBasis.repr (FD.localBasis ()) ()
  have hFC := (basis_single_smul _ _ FD.localBasis (FC.localBasis ())).symm
  have hFD := (basis_single_smul _ _ FC.localBasis (FD.localBasis ())).symm
  have hmul : (a * c) • FC.localBasis () = FC.localBasis () := by
    rw [mul_smul, ← hFD, hFC.symm]
  have hac : a * c = 1 := by
    have h1 : FC.localBasis.repr ((a * c) • FC.localBasis ()) () =
        FC.localBasis.repr (FC.localBasis ()) () := by rw [hmul]
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_eq_same, mul_one] using h1
  set u : (LocalRing V p.val)ˣ := Units.mkOfMulEqOne a c hac
  have hu : FC.localBasis () = (u : LocalRing V p.val) • FD.localBasis () := hFC
  have hF : localTopMap V p.val (FC.localBasis ()) =
      (localToField V p.val).toRingHom (u : LocalRing V p.val) •
        localTopMap V p.val (FD.localBasis ()) := by
    rw [hu]
    exact LinearMap.map_smulₛₗ _ _ _
  have hrat : FC.rationalBasis () =
      (localToField V p.val).toRingHom (u : LocalRing V p.val) • FD.rationalBasis () := by
    rw [FC.normalized, hF, ← FD.normalized]
  have hrecon : (FC.rationalBasis.repr eta ()) • FC.rationalBasis () = eta :=
    basis_single_smul _ _ _ _
  have heta : (FC.rationalBasis.repr eta () *
      (localToField V p.val).toRingHom (u : LocalRing V p.val)) • FD.rationalBasis () = eta := by
    rw [mul_smul, ← hrat, hrecon]
  have he : FD.rationalBasis.repr eta () = FC.rationalBasis.repr eta () *
      (localToField V p.val).toRingHom (u : LocalRing V p.val) := by
    have h1 : FD.rationalBasis.repr eta () = FD.rationalBasis.repr
        ((FC.rationalBasis.repr eta () *
          (localToField V p.val).toRingHom (u : LocalRing V p.val)) • FD.rationalBasis ()) () := by
      rw [heta]
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_eq_same, mul_one] using h1
  have heC : FC.rationalBasis.repr eta () ≠ 0 := by
    intro hz
    apply hne
    rw [← hrecon, hz, zero_smul]
  have hσ : (localToField V p.val).toRingHom =
      algebraMap (LocalRing V p.val) (FunctionField V) := rfl
  have hord0 : V.X.left.ord ((localToField V p.val).toRingHom (u : LocalRing V p.val))
      p.val = 0 := by
    rw [hσ]
    exact V.X.left.ord_algebraMap_eq_zero_of_isUnit u.isUnit
  have hσu : (localToField V p.val).toRingHom (u : LocalRing V p.val) ≠ 0 := by
    rw [hσ]
    exact V.X.left.algebraMap_functionField_ne_zero u.isUnit.ne_zero
  have hmul2 := V.X.left.ord_mul (x := p.val) heC hσu
  rw [hord0, add_zero] at hmul2
  rw [he, hmul2]

/-- The canonical divisor does not depend on the chosen frames: for a field $k$ of characteristic
zero and a normal variety $V$ of dimension $n$ over $k$ (integral, Noetherian, separated, locally of
finite type and quasi-compact, with integrally closed local rings), two canonical data on $V$ with
the same rational top form have the same canonical divisor. -/
public theorem canonical_frame_independence (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (V : NormalVariety k n) (C D : CanonicalData V) (same : C.form = D.form) :
    canonicalDivisor C = canonicalDivisor D := by
  refine Finsupp.ext fun p => ?_
  change canonicalCoefficient V C.form C.frames p = canonicalCoefficient V D.form D.frames p
  rw [same]
  exact ord_repr_eq_of_form_eq k n V p D.form D.nonzero (C.frames p) (D.frames p)

end WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted
