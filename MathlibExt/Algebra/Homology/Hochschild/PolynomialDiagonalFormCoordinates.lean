/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDifferentialFormComplexComparison
public import MathlibExt.RingTheory.MvPolynomial.EnvelopingDiagonalCotangentLifts
public import MathlibExt.LinearAlgebra.ExteriorPower.Semilinear

/-!
# form coordinates of arbitrary diagonal Koszul wedges

The diagonal free module maps semilinearly to the original cotangent module
by multiplying its original enveloping coefficients. The coefficient form
coordinate equivalence sends every diagonal wedge to the wedge of these
cotangent images. The proof uses the native arbitrary-index exterior
basis and needs no finite variable set or coefficient flatness.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)

/-- The semilinear cotangent image of one diagonal free coordinate. -/
def diagonalCotangentSemilinearSingle (i : σ) :
    MvPolynomial.PolynomialEnveloping k σ →ₛₗ[(MvPolynomial.diagonalMultiplication k σ).toRingHom]
      KaehlerDifferential k (MvPolynomial σ k) where
  toFun e := MvPolynomial.diagonalMultiplication k σ e •
    KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i)
  map_add' e e' := by rw [map_add, add_smul]
  map_smul' e e' := by
    simp only [smul_eq_mul, map_mul, mul_smul,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- Multiply the original enveloping coordinates and keep the original
universal variable differentials. -/
def diagonalCotangentSemilinearMap :
    (σ →₀ MvPolynomial.PolynomialEnveloping k σ) →ₛₗ[(MvPolynomial.diagonalMultiplication k σ).toRingHom]
      KaehlerDifferential k (MvPolynomial σ k) :=
  Finsupp.lsum ℕ (diagonalCotangentSemilinearSingle k σ)

/-- The semilinear map is the same coordinate function as the
ground-linear conormal map. -/
theorem diagonalCotangentSemilinearMap_coordinates
    (x : σ →₀ MvPolynomial.PolynomialEnveloping k σ) :
    diagonalCotangentSemilinearMap k σ x = MvPolynomial.diagonalCotangentCoordinates k σ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | single i e =>
      rw [diagonalCotangentSemilinearMap, Finsupp.lsum_single,
        MvPolynomial.diagonalCotangentCoordinates_single]
      change MvPolynomial.diagonalMultiplication k σ e •
        KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i) = _
      rfl

/-- The original unit variable maps to the differential `dX`. -/
theorem diagonalCotangentSemilinearMap_single (i : σ) :
    diagonalCotangentSemilinearMap k σ
        (Finsupp.single i (1 : MvPolynomial.PolynomialEnveloping k σ)) =
      KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i) := by
  rw [diagonalCotangentSemilinearMap, Finsupp.lsum_single]
  change MvPolynomial.diagonalMultiplication k σ (1 : MvPolynomial.PolynomialEnveloping k σ) •
    KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i) = _
  rw [map_one, one_smul]

/-- The exterior cotangent map in the native ground-restricted
diagonal degree and the original form degree. -/
def diagonalCotangentExteriorGround (n : ℕ) :
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) →ₗ[k]
      (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) := by
  letI : Module k
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
    Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
  exact
    { toFun := exteriorPower.mapSemilinear (MvPolynomial.diagonalMultiplication k σ).toRingHom
        (diagonalCotangentSemilinearMap k σ) n
      map_add' := map_add _
      map_smul' := by
        intro c x
        change exteriorPower.mapSemilinear (MvPolynomial.diagonalMultiplication k σ).toRingHom
          (diagonalCotangentSemilinearMap k σ) n
          (algebraMap k (MvPolynomial.PolynomialEnveloping k σ) c • x) = _
        rw [map_smulₛₗ]
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.id_apply]
        rw [(MvPolynomial.diagonalMultiplication k σ).commutes,
          IsScalarTower.algebraMap_smul (MvPolynomial σ k)] }

/-- Native exterior point values on the original scaled variable wedges. -/
private theorem diagonalCotangentExteriorGround_smul_basis
    (n : ℕ) (e : MvPolynomial.PolynomialEnveloping k σ) (a : Fin n → σ) :
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    diagonalCotangentExteriorGround k σ n
        (e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n
          (fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ))) =
      MvPolynomial.diagonalMultiplication k σ e •
        exteriorPower.ιMulti (MvPolynomial σ k) n
          (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j))) := by
  letI : Module k
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
    Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
  let φ : MvPolynomial.PolynomialEnveloping k σ →+* MvPolynomial σ k :=
    (MvPolynomial.diagonalMultiplication k σ).toRingHom
  let f₀ : (σ →₀ MvPolynomial.PolynomialEnveloping k σ) →ₛₗ[φ]
      KaehlerDifferential k (MvPolynomial σ k) := diagonalCotangentSemilinearMap k σ
  let F :
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) →ₛₗ[φ]
          (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) :=
    exteriorPower.mapSemilinear φ f₀ n
  let v : Fin n → (σ →₀ MvPolynomial.PolynomialEnveloping k σ) :=
    fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ)
  let ω : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) :=
    exteriorPower.ιMulti (MvPolynomial σ k) n
      (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j)))
  have hvec : (fun j : Fin n => f₀ (v j)) =
      (fun j : Fin n =>
        KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j))) := by
    funext j
    exact diagonalCotangentSemilinearMap_single k σ (a j)
  have hmap := exteriorPower.mapSemilinear_ιMulti
    (R := MvPolynomial.PolynomialEnveloping k σ) (S := MvPolynomial σ k)
    (M := σ →₀ MvPolynomial.PolynomialEnveloping k σ)
    (N := KaehlerDifferential k (MvPolynomial σ k)) φ f₀ n v
  have htail := congrArg
    (fun l : Fin n → KaehlerDifferential k (MvPolynomial σ k) =>
      exteriorPower.ιMulti (MvPolynomial σ k) n l) hvec
  have hw := hmap.trans htail
  have hφ : φ e = MvPolynomial.diagonalMultiplication k σ e :=
    congrFun (AlgHom.coe_toRingHom (MvPolynomial.diagonalMultiplication k σ)) e
  have hsmul := F.map_smulₛₗ e
    (exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n v)
  have hscaled := hsmul.trans
    ((congrArg
      (fun z : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) =>
        φ e • z) hw).trans
      (congrArg (fun r : MvPolynomial σ k => r • ω) hφ))
  have hground :
      diagonalCotangentExteriorGround k σ n
          (e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n v) =
        F (e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n v) := rfl
  exact hground.trans hscaled

section Coefficients

variable (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

/-- Original scaled variable wedges have their multiplied
enveloping coefficient and original differential-variable tail. -/
theorem symmetricCoefficientFormDegreeEquiv_mk_smul_basis
    (n : ℕ) (m : M) (e : MvPolynomial.PolynomialEnveloping k σ) (a : Fin n → σ) :
    letI := Symmetric.opModule (MvPolynomial σ k) M
    letI := Symmetric.actionsComm (MvPolynomial σ k) M
    letI := Symmetric.kOpComm k (MvPolynomial σ k) M
    letI := Symmetric.kOpTower k (MvPolynomial σ k) M
    letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    symmetricCoefficientFormDegreeEquiv k σ M n
      (TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m
        (e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n
          (fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ)))) =
      (MvPolynomial.diagonalMultiplication k σ e • m) ⊗ₜ[MvPolynomial σ k]
        exteriorPower.ιMulti (MvPolynomial σ k) n
          (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j))) := by
  letI := Symmetric.opModule (MvPolynomial σ k) M
  letI := Symmetric.actionsComm (MvPolynomial σ k) M
  letI := Symmetric.kOpComm k (MvPolynomial σ k) M
  letI := Symmetric.kOpTower k (MvPolynomial σ k) M
  letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
  letI : Module k
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
    Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
  change KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n
    (coefficientFreeExteriorEquiv k σ M n _) = _
  rw [coefficientFreeExteriorEquiv_mk_smul_basis,
    KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_tmul_basis]
  have he : MulOpposite.op e • m = MvPolynomial.diagonalMultiplication k σ e • m :=
    symmetricRightEnvelopingAction_multiplication k σ M e m
  rw [he]

/-- Original unscaled variable wedges have the original coefficient head. -/
theorem symmetricCoefficientFormDegreeEquiv_mk_basis
    (n : ℕ) (m : M) (a : Fin n → σ) :
    letI := Symmetric.opModule (MvPolynomial σ k) M
    letI := Symmetric.actionsComm (MvPolynomial σ k) M
    letI := Symmetric.kOpComm k (MvPolynomial σ k) M
    letI := Symmetric.kOpTower k (MvPolynomial σ k) M
    letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    symmetricCoefficientFormDegreeEquiv k σ M n
      (TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m
        (exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n
          (fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ)))) =
      m ⊗ₜ[MvPolynomial σ k] exteriorPower.ιMulti (MvPolynomial σ k) n
        (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j))) := by
  simpa only [map_one, one_smul] using
    symmetricCoefficientFormDegreeEquiv_mk_smul_basis k σ M n m
      (1 : MvPolynomial.PolynomialEnveloping k σ) a

/-- Every original diagonal exterior element has its multiplied
cotangent coordinates, including sums and arbitrary enveloping coefficients. -/
theorem symmetricCoefficientFormDegreeEquiv_mk
    (n : ℕ) (m : M)
    (x : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
    letI := Symmetric.opModule (MvPolynomial σ k) M
    letI := Symmetric.actionsComm (MvPolynomial σ k) M
    letI := Symmetric.kOpComm k (MvPolynomial σ k) M
    letI := Symmetric.kOpTower k (MvPolynomial σ k) M
    letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    symmetricCoefficientFormDegreeEquiv k σ M n
      (TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m x) =
      m ⊗ₜ[MvPolynomial σ k]
        exteriorPower.mapSemilinear (MvPolynomial.diagonalMultiplication k σ).toRingHom
          (diagonalCotangentSemilinearMap k σ) n x := by
  classical
  letI : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  letI := Symmetric.opModule (MvPolynomial σ k) M
  letI := Symmetric.actionsComm (MvPolynomial σ k) M
  letI := Symmetric.kOpComm k (MvPolynomial σ k) M
  letI := Symmetric.kOpTower k (MvPolynomial σ k) M
  letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
  letI : Module k
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
    Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
  let S := symmetricCoefficientFormDegreeEquiv k σ M n
  let q := TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
    (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m
  let G := diagonalCotangentExteriorGround k σ n
  let t₀ := TensorProduct.mk (MvPolynomial σ k) M
    (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) m
  let t := t₀.restrictScalars k
  let L :
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) →ₗ[k]
          M ⊗[MvPolynomial σ k] (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) :=
    S.toLinearMap.comp q
  let T :
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) →ₗ[k]
          M ⊗[MvPolynomial σ k] (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) :=
    t.comp G
  have hSourceValue
      (y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
      L y = S (q y) := by
    have hcomp := LinearMap.comp_apply S.toLinearMap q y
    have hequiv := congrFun (LinearEquiv.coe_toLinearMap S) (q y)
    exact hcomp.trans hequiv
  have hTargetValue
      (y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
      T y = m ⊗ₜ[MvPolynomial σ k] G y := by
    have hcomp := LinearMap.comp_apply t G y
    have hrestrict := LinearMap.restrictScalars_apply k t₀ (G y)
    exact hcomp.trans hrestrict
  have hGroundValue
      (y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
      G y = exteriorPower.mapSemilinear (MvPolynomial.diagonalMultiplication k σ).toRingHom
        (diagonalCotangentSemilinearMap k σ) n y := rfl
  have hDesired : L x = T x := by
    generalize hL : L = L'
    generalize hT : T = T'
    let b := Module.Basis.exteriorPower
      (R := MvPolynomial.PolynomialEnveloping k σ)
      (M := σ →₀ MvPolynomial.PolynomialEnveloping k σ) (I := σ) n
      (Finsupp.basisSingleOne (R := MvPolynomial.PolynomialEnveloping k σ) (ι := σ))
    have h : ∀ a : Set.powersetCard σ n →₀ MvPolynomial.PolynomialEnveloping k σ,
        L' (Finsupp.linearCombination (MvPolynomial.PolynomialEnveloping k σ) b a) =
          T' (Finsupp.linearCombination (MvPolynomial.PolynomialEnveloping k σ) b a) := by
      intro a
      induction a using Finsupp.induction_linear with
      | zero => simp only [map_zero]
      | add a a' ha ha' => simp only [map_add, ha, ha']
      | single s e =>
          rw [Finsupp.linearCombination_single]
          simp only [b, exteriorPower.coe_basis, exteriorPower.ιMulti_family, Finsupp.coe_basisSingleOne]
          let a : Fin n → σ := fun j => Set.powersetCard.ofFinEmbEquiv.symm s j
          let w : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
              (σ →₀ MvPolynomial.PolynomialEnveloping k σ) :=
            e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n
              (fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ))
          let ω : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) :=
            exteriorPower.ιMulti (MvPolynomial σ k) n
              (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j)))
          change L' w = T' w
          have hNativeLeft := symmetricCoefficientFormDegreeEquiv_mk_smul_basis k σ M n m e a
          have hNativeRight := diagonalCotangentExteriorGround_smul_basis k σ n e a
          have hleft := (LinearMap.congr_fun hL w).symm.trans
            ((hSourceValue w).trans hNativeLeft)
          have hright := congrArg
            (fun z : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) =>
              m ⊗ₜ[MvPolynomial σ k] z) hNativeRight
          have htensor :
              (MvPolynomial.diagonalMultiplication k σ e • m) ⊗ₜ[MvPolynomial σ k] ω =
                m ⊗ₜ[MvPolynomial σ k] (MvPolynomial.diagonalMultiplication k σ e • ω) :=
            TensorProduct.smul_tmul (R := MvPolynomial σ k) (R' := MvPolynomial σ k)
              (M := M) (N := ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)))
              (MvPolynomial.diagonalMultiplication k σ e) m ω
          exact hleft.trans
            (htensor.trans
              (hright.symm.trans ((hTargetValue w).symm.trans (LinearMap.congr_fun hT w))))
    have hx := h (b.repr x)
    have hrepr := Module.Basis.linearCombination_repr
      (R := MvPolynomial.PolynomialEnveloping k σ)
      (M := ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) b x
    have hLrepr := congrArg
      (fun y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ) => L' y) hrepr
    have hTrepr := congrArg
      (fun y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ) => T' y) hrepr
    exact hLrepr.symm.trans (hx.trans hTrepr)
  exact (hSourceValue x).symm.trans
    (hDesired.trans
      ((hTargetValue x).trans
        (congrArg
          (fun z : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) =>
            m ⊗ₜ[MvPolynomial σ k] z) (hGroundValue x))))

/-- An arbitrary original diagonal wedge becomes the wedge of its cotangent images. -/
theorem symmetricCoefficientFormDegreeEquiv_mk_ιMulti
    (n : ℕ) (m : M) (a : Fin n → (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
    letI := Symmetric.opModule (MvPolynomial σ k) M
    letI := Symmetric.actionsComm (MvPolynomial σ k) M
    letI := Symmetric.kOpComm k (MvPolynomial σ k) M
    letI := Symmetric.kOpTower k (MvPolynomial σ k) M
    letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    symmetricCoefficientFormDegreeEquiv k σ M n
      (TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m
        (exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n a)) =
      m ⊗ₜ[MvPolynomial σ k] exteriorPower.ιMulti (MvPolynomial σ k) n
        (fun j => diagonalCotangentSemilinearMap k σ (a j)) := by
  rw [symmetricCoefficientFormDegreeEquiv_mk, exteriorPower.mapSemilinear_ιMulti]

end Coefficients

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
