/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Perfectoid.BDeRham
public import Mathlib.RingTheory.WittVector.Compare
public import MathlibExt.AlgebraicGeometry.HodgeTateComparison
public import MathlibExt.RingTheory.AdicCompletion.Localization

/-!
# Galois action on the de Rham period ring of `ℂ_p`

The Galois group `Gal(\bar{ℚ}_p/ℚ_p)` acts on `𝓞_ℂ_p` by the completed action on `ℂ_p`
(`integralGalois`), on the tilt `𝓞_ℂ_p^♭` by functoriality (`tiltGalois`), and on
`W(𝓞_ℂ_p^♭)[1/p]` by functoriality of Witt vectors and localization (`preDeRhamGalois`). The last
action fixes the image of `ℚ_p`, which comes from `ℤ_p = W(𝔽_p) → W(𝓞_ℂ_p^♭)`
(`preDeRhamGalois_comp_padicToPreDeRham`).

Given the `p`-adic completeness of `𝓞_ℂ_p`, Mathlib's `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p`, the
`(ker θ)`-adic completion of `W(𝓞_ℂ_p^♭)[1/p]`, is a `ℚ_p`-algebra (`BdRPlus`) with the filtration
`Fil^j B_dR^+`, the kernel of the projection to `W(𝓞_ℂ_p^♭)[1/p] ⧸ (ker θ)^j` (`fil`). An element of
the Galois group whose action on `W(𝓞_ℂ_p^♭)[1/p]` preserves `ker θ` acts on `B_dR^+` by
continuity, `ℚ_p`-linearly (`bdRPlusGaloisLinear`). For a scheme `A` over a subfield `F` of
`\bar{ℚ}_p` and `V = H¹_ét(A_{\bar{ℚ}_p}, ℚ_p)`, `filDeRham` is
`Fil^j D_dR(V) = (Fil^j B_dR^+ ⊗ V)^{G_F}` for `j ≥ 0`, given that every Galois element preserves
`ker θ`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open HodgeTateComparison GeometricAdicGaloisOperators AdicLinearFunctoriality
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

theorem norm_completionGalois (σ : Galois p) (x : PadicComplex p) :
    ‖completionGalois p σ x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_completionGalois p σ).norm continuous_norm
  | ih a =>
    have h := completionGalois_coe p σ a
    change completionGalois p σ (a : PadicComplex p) = ((σ a : PadicAlgCl p) : PadicComplex p)
      at h
    rw [h, PadicComplex.norm_extends, PadicComplex.norm_extends, closure_norm_apply]

theorem mem_padicComplexInt_iff (x : PadicComplex p) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm]
  let := Valued.toNormedField (PadicComplex p) NNReal
  exact (Valued.toNormedField.norm_le_one_iff (x := x)).symm

instance padicComplexInt_fact_not_isUnit_p : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) := by
  refine ⟨fun h => ?_⟩
  have h1 := (PadicComplexInt.integers p).isUnit_iff_valuation_eq_one.mp h
  rw [map_natCast, PadicComplex.valuation_p] at h1
  have h2 := h1.symm
  have hp : (1 : NNReal) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [eq_div_iff (by positivity), one_mul] at h2
  exact hp.ne' h2

/- The Galois action on `𝓞_ℂ_p`. -/
def integralGalois (σ : Galois p) : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p] :=
  ((completionGalois p σ).toRingHom.comp (𝓞_ℂ_[p]).subtype).codRestrict (𝓞_ℂ_[p]) fun x => by
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [mem_padicComplexInt_iff]
    change ‖completionGalois p σ (x : PadicComplex p)‖ ≤ 1
    rw [norm_completionGalois, ← mem_padicComplexInt_iff]
    exact x.2

/- The Galois action on the tilt. -/
def tiltGalois (σ : Galois p) : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p :=
  Perfection.map p (Ideal.quotientMap (Ideal.span {(p : 𝓞_ℂ_[p])}) (integralGalois p σ) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span rfl))

abbrev Ainf := WittVector p (PreTilt 𝓞_ℂ_[p] p)

abbrev PreDeRham := Localization.Away (p : Ainf p)

/- The Galois action on `W(𝓞♭)[1/p]`. -/
def preDeRhamGalois (σ : Galois p) : PreDeRham p →+* PreDeRham p :=
  Localization.awayLift
    ((algebraMap (Ainf p) (PreDeRham p)).comp (WittVector.map (tiltGalois p σ))) (p : Ainf p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : Ainf p))

theorem preDeRhamGalois_comp_algebraMap (σ : Galois p) :
    (preDeRhamGalois p σ).comp (algebraMap (Ainf p) (PreDeRham p)) =
      (algebraMap (Ainf p) (PreDeRham p)).comp (WittVector.map (tiltGalois p σ)) :=
  IsLocalization.Away.lift_comp (p : Ainf p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : Ainf p))

/- The ring map `ℤ_p = W(𝔽_p) → W(𝓞♭)`. -/
def padicIntToAinf : ℤ_[p] →+* Ainf p :=
  (WittVector.map (ZMod.castHom dvd_rfl (PreTilt 𝓞_ℂ_[p] p))).comp
    (WittVector.equiv p).symm.toRingHom

/- The ring map `ℚ_p → W(𝓞♭)[1/p]`. -/
def padicToPreDeRham : ℚ_[p] →+* PreDeRham p :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p])
    (g := (algebraMap (Ainf p) (PreDeRham p)).comp (padicIntToAinf p)) fun x => by
      obtain ⟨x, hx⟩ := x
      have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
      change IsUnit (((algebraMap (Ainf p) (PreDeRham p)).comp (padicIntToAinf p)) x)
      rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast]
      refine ((PadicInt.unitCoeff hx0).isUnit.map _).mul (IsUnit.pow _ ?_)
      simpa using IsLocalization.Away.algebraMap_isUnit (p : Ainf p)

theorem preDeRhamGalois_comp_padicToPreDeRham (σ : Galois p) :
    (preDeRhamGalois p σ).comp (padicToPreDeRham p) = padicToPreDeRham p := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) ?_
  rw [RingHom.comp_assoc, padicToPreDeRham, IsLocalization.lift_comp, ← RingHom.comp_assoc,
    preDeRhamGalois_comp_algebraMap, RingHom.comp_assoc]
  congr 1
  ext x n
  simp only [padicIntToAinf, RingHom.coe_comp, Function.comp_apply, WittVector.map_coeff]
  exact congrArg (fun f : ZMod p →+* PreTilt 𝓞_ℂ_[p] p => f _)
    (RingHom.ext_zmod ((tiltGalois p σ).comp (ZMod.castHom dvd_rfl _)) (ZMod.castHom dvd_rfl _))

section Completion

variable [IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]]

/- The kernel of `θ : W(𝓞♭)[1/p] → ℂ_p`. -/
abbrev thetaKer : Ideal (PreDeRham p) := RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)

/- `B_dR^+`, with its `ℚ_p`-algebra structure. -/
def BdRPlus : Type := BDeRhamPlus 𝓞_ℂ_[p] p

instance : CommRing (BdRPlus p) := inferInstanceAs (CommRing (BDeRhamPlus 𝓞_ℂ_[p] p))

/- The canonical map `W(𝓞♭)[1/p] → B_dR^+`. -/
def ofPreDeRham : PreDeRham p →+* BdRPlus p :=
  algebraMap (PreDeRham p) (AdicCompletion (thetaKer p) (PreDeRham p))

instance : Algebra ℚ_[p] (BdRPlus p) := ((ofPreDeRham p).comp (padicToPreDeRham p)).toAlgebra

/- The projection `B_dR^+ → W(𝓞♭)[1/p] ⧸ (ker θ)^n`. -/
def evalBdR (n : ℕ) : BdRPlus p →+* PreDeRham p ⧸ thetaKer p ^ n :=
  (AdicCompletion.evalₐ (thetaKer p) n).toRingHom

/- `Fil^j B_dR^+`. -/
def fil (j : ℕ) : Ideal (BdRPlus p) := RingHom.ker (evalBdR p j)

theorem pow_le_comap {f : PreDeRham p →+* PreDeRham p} (h : thetaKer p ≤ (thetaKer p).comap f)
    (n : ℕ) : thetaKer p ^ n ≤ (thetaKer p ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h) n

/- The Galois action on `B_dR^+`. -/
def bdRPlusGalois (σ : Galois p) (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)) :
    BdRPlus p →+* BdRPlus p :=
  AdicCompletion.liftRingHom (thetaKer p)
    (fun n => (Ideal.quotientMap (thetaKer p ^ n) (preDeRhamGalois p σ)
      (pow_le_comap p h n)).comp (evalBdR p n))
    (fun {m n} hle => by
      ext x
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalBdR p n x)
      have hm : evalBdR p m x = Ideal.Quotient.mk _ y := by
        change AdicCompletion.evalₐ (thetaKer p) m x = _
        rw [← AdicCompletion.factorPow_evalₐ (thetaKer p) hle x]
        change Ideal.Quotient.factorPow _ hle (evalBdR p n x) = _
        rw [← hy]
        simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
      simp only [RingHom.coe_comp, Function.comp_apply, hm, ← hy, Ideal.quotientMap_mk,
        Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk])

theorem bdRPlusGalois_ofPreDeRham (σ : Galois p)
    (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)) (x : PreDeRham p) :
    bdRPlusGalois p σ h (ofPreDeRham p x) = ofPreDeRham p (preDeRhamGalois p σ x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  change AdicCompletion.evalₐ _ n (AdicCompletion.liftRingHom _ _ _ _) = _
  rw [AdicCompletion.evalₐ_liftRingHom, RingHom.comp_apply]
  change Ideal.quotientMap _ _ (pow_le_comap p h n)
      (AdicCompletion.evalₐ (thetaKer p) n (AdicCompletion.of (thetaKer p) (PreDeRham p) x)) =
    AdicCompletion.evalₐ (thetaKer p) n
      (AdicCompletion.of (thetaKer p) (PreDeRham p) (preDeRhamGalois p σ x))
  rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

/- The Galois action on `B_dR^+`, as a `ℚ_p`-linear map. -/
def bdRPlusGaloisLinear (σ : Galois p)
    (h : thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)) :
    BdRPlus p →ₗ[ℚ_[p]] BdRPlus p where
  toFun := bdRPlusGalois p σ h
  map_add' := map_add _
  map_smul' c x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    change bdRPlusGalois p σ h (ofPreDeRham p (padicToPreDeRham p c)) =
      ofPreDeRham p (padicToPreDeRham p c)
    rw [bdRPlusGalois_ofPreDeRham, ← RingHom.comp_apply (preDeRhamGalois p σ),
      preDeRhamGalois_comp_padicToPreDeRham]

end Completion

section Cohomology

variable [IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]]
variable (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (A : Over (Spec (CommRingCat.of F)))

/- `H¹_ét(A_{\bar F}, ℚ_p)`. -/
abbrev H1 : Type 1 := AdicCohomology p (geometricFibre A (PadicAlgCl p)) 1

/- The action of `Gal(\bar F / F)` on `H¹_ét(A_{\bar F}, ℚ_p)`. -/
def h1Galois (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) : H1 p F A →ₗ[ℚ_[p]] H1 p F A :=
  continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p)
    (galoisSchemeOperator A (PadicAlgCl p) σ) 1

/- `Fil^j D_dR` for `j ≥ 0`. -/
def filDeRham (h : ∀ τ : Galois p, thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p τ))
    (j : ℕ) : Submodule ℚ_[p] (BdRPlus p ⊗[ℚ_[p]] H1 p F A) :=
  LinearMap.range (TensorProduct.map ((fil p j).restrictScalars ℚ_[p]).subtype
      (LinearMap.id : H1 p F A →ₗ[ℚ_[p]] H1 p F A)) ⊓
    ⨅ σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p,
      LinearMap.eqLocus
        (TensorProduct.map (bdRPlusGaloisLinear p (σ.restrictScalars ℚ_[p]) (h _))
          (h1Galois p F A σ)) LinearMap.id

end Cohomology

end MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison
