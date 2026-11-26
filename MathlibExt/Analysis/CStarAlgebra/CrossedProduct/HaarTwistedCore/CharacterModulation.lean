/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Topology.Algebra.PontryaginDual.Pairing
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.StarRing
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Gauge

/-!
# Unitary-character modulation of twisted convolution

Let G be a locally compact topological group with regular left Haar measure μ, A a nonunital
complex C-star algebra, and α a point-norm action. For a continuous unitary character
χ∈PontryaginDual G, define Mχf(s)=χ(s)•f(s) on compactly supported coefficients. These maps
are star-algebra automorphisms of the Haar twisted-convolution core, satisfy Mχη=Mχ∘Mη, and
preserve the L¹ gauge ∫ s, ‖f(s)‖ ∂μ. This is the character formula for the dual action in
Blackadar, Section10.1.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported CStarAlgebra

namespace HaarTwistedCore

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] (alpha : PointNormCStarAction G A)

/-- **Modulation by a unitary character.**

For a point-norm action α on A, Haar measure μ, a continuous unitary character χ of G and
f∈Cc(G,A), character modulation is Mχf(s)=χ(s)•f(s). The resulting coefficient is continuous
and compactly supported.
-/
def characterModulation (chi : PontryaginDual G) (f : Carrier mu alpha) : Carrier mu alpha where
  toCc :=
    { toFun := fun s => (chi s : ℂ) • f s
      continuous_toFun := (continuous_subtype_val.comp (map_continuous chi)).smul
        (map_continuous (toCc mu alpha f))
      hasCompactSupport' := HasCompactSupport.intro' (toCc mu alpha f).hasCompactSupport
        (isClosed_tsupport (toCc mu alpha f)) (fun s hs => by
          rw [image_eq_zero_of_notMem_tsupport hs, smul_zero]) }

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [mu.IsHaarMeasure] [mu.Regular] in
/-- **Character-modulated coefficient value.**

For χ∈PontryaginDual G and compactly supported f:G→A in the Haar core for (μ,α),
`characterModulation μ α χ f s = (χ s : ℂ) • f s` for every s∈G.
-/
@[simp]
theorem characterModulation_apply (chi : PontryaginDual G) (f : Carrier mu alpha) (s : G) :
    characterModulation mu alpha chi f s = (chi s : ℂ) • f s := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [mu.IsHaarMeasure] [mu.Regular] in
/-- **Composition of character modulations.**

For unitary characters χ,η of G and a Haar-core coefficient f, Mχηf=Mχ(Mηf), where
Mχf(s)=χ(s)•f(s).
-/
theorem characterModulation_mul_character (chi eta : PontryaginDual G) (f : Carrier mu alpha) :
    characterModulation mu alpha (chi * eta) f =
      characterModulation mu alpha chi (characterModulation mu alpha eta f) := by
  apply ext mu alpha
  intro s
  change ((chi * eta) s : ℂ) • f s = (chi s : ℂ) • ((eta s : ℂ) • f s)
  rw [smul_smul]
  rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [mu.IsHaarMeasure] [mu.Regular] in
/-- **Trivial character acts identically.**

For every coefficient f in the Haar twisted-convolution core, M1f=f, where Mχf(s)=χ(s)•f(s).
-/
@[simp]
theorem characterModulation_one (f : Carrier mu alpha) : characterModulation mu alpha 1 f = f := by
  apply ext mu alpha
  intro s
  change (1 : ℂ) • f s = f s
  exact one_smul ℂ (f s)

omit [LocallyCompactSpace G] [mu.Regular] in
/-- **Character modulation preserves convolution.**

For compactly supported A-valued coefficients f,h, a point-norm action α and a unitary
character χ of G, Mχ(f*h)=Mχf*Mχh for Haar twisted convolution, where Mχf(s)=χ(s)•f(s).
-/
theorem characterModulation_convolution (chi : PontryaginDual G) (f h : Carrier mu alpha) :
    characterModulation mu alpha chi (convolution mu alpha f h) =
      convolution mu alpha (characterModulation mu alpha chi f) (characterModulation mu alpha chi h) := by
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  apply ext mu alpha
  intro s
  change (chi s : ℂ) • (∫ t : G, f t * alpha t (h (t⁻¹ * s)) ∂mu) =
    ∫ t : G, ((chi t : ℂ) • f t) * alpha t ((chi (t⁻¹ * s) : ℂ) • h (t⁻¹ * s)) ∂mu
  rw [← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change (chi s : ℂ) • (f t * alpha t (h (t⁻¹ * s))) =
      ((chi t : ℂ) • f t) * alpha t ((chi (t⁻¹ * s) : ℂ) • h (t⁻¹ * s))
    have hcircle : chi t * chi (t⁻¹ * s) = chi s := by
      rw [← map_mul, mul_inv_cancel_left]
    have hscalar : (chi t : ℂ) * (chi (t⁻¹ * s) : ℂ) = (chi s : ℂ) := by
      calc
        (chi t : ℂ) * (chi (t⁻¹ * s) : ℂ) =
            ((chi t * chi (t⁻¹ * s) : Circle) : ℂ) :=
          (Circle.coe_mul (chi t) (chi (t⁻¹ * s))).symm
        _ = (chi s : ℂ) := congrArg (fun z : Circle => (z : ℂ)) hcircle
    rw [alpha.apply_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hscalar]

omit [BorelSpace G] [mu.IsHaarMeasure] [mu.Regular] in
/-- **Character modulation preserves involution.**

For a Haar-core coefficient f and unitary character χ, Mχ(f*)=(Mχf)*, with Mχf(s)=χ(s)•f(s)
and f* the modularly weighted twisted involution.
-/
theorem characterModulation_crossedStar (chi : PontryaginDual G) (f : Carrier mu alpha) :
    characterModulation mu alpha chi (crossedStar mu alpha f) =
      crossedStar mu alpha (characterModulation mu alpha chi f) := by
  apply ext mu alpha
  intro s
  have hu : PontryaginDual.unitaryCharacter chi s⁻¹ = (PontryaginDual.unitaryCharacter chi s)⁻¹ :=
    map_inv (PontryaginDual.unitaryCharacter chi) s
  have hscalar : star (chi s⁻¹ : ℂ) = (chi s : ℂ) := by
    have h : star (PontryaginDual.unitaryCharacter chi s⁻¹ : ℂ) =
        (PontryaginDual.unitaryCharacter chi s : ℂ) := by
      rw [hu]
      change star (star (PontryaginDual.unitaryCharacter chi s : ℂ)) = _
      exact star_star _
    simpa only [PontryaginDual.unitaryCharacter_coe] using h
  simp only [characterModulation_apply, crossedStar_apply, star_smul, alpha.apply_smul, hscalar, smul_smul]
  congr 1
  exact mul_comm _ _

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [mu.IsHaarMeasure] [mu.Regular] in
/-- **L¹ gauge is invariant under unitary characters.**

For a compactly supported coefficient f and unitary character χ, `l1Gauge μ α
(characterModulation μ α χ f) = l1Gauge μ α f`, since the gauge is ∫ s, ‖f(s)‖ ∂μ and
‖χ(s)‖=1.
-/
theorem l1Gauge_characterModulation (chi : PontryaginDual G) (f : Carrier mu alpha) :
    l1Gauge mu alpha (characterModulation mu alpha chi f) = l1Gauge mu alpha f := by
  unfold l1Gauge
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    change ‖(chi s : ℂ) • f s‖ = ‖f s‖
    rw [norm_smul, Circle.norm_coe, one_mul]

/-- **Character automorphism of the Haar convolution core.**

For χ∈PontryaginDual G, the map Mχf(s)=χ(s)•f(s) is a complex star-algebra automorphism of the
Haar twisted-convolution core for (μ,α). Its inverse is modulation by χ⁻¹.
-/
def characterModulationEquiv (chi : PontryaginDual G) : Carrier mu alpha ≃⋆ₐ[ℂ] Carrier mu alpha where
  toFun := characterModulation mu alpha chi
  invFun := characterModulation mu alpha chi⁻¹
  left_inv f := by
    rw [← characterModulation_mul_character, inv_mul_cancel, characterModulation_one]
  right_inv f := by
    rw [← characterModulation_mul_character, mul_inv_cancel, characterModulation_one]
  map_add' f h := by
    apply ext mu alpha
    intro s
    change (chi s : ℂ) • (f s + h s) = (chi s : ℂ) • f s + (chi s : ℂ) • h s
    exact smul_add _ _ _
  map_mul' := characterModulation_convolution mu alpha chi
  map_smul' c f := by
    apply ext mu alpha
    intro s
    change (chi s : ℂ) • (c • f s) = c • ((chi s : ℂ) • f s)
    exact smul_comm _ _ _
  map_star' := characterModulation_crossedStar mu alpha chi

omit [mu.Regular] in
/-- **Evaluation of the character automorphism.**

For a continuous unitary character χ of G and compactly supported coefficient f,
`characterModulationEquiv μ α χ f s = (χ s : ℂ) • f s`.
-/
@[simp]
theorem characterModulationEquiv_apply (chi : PontryaginDual G) (f : Carrier mu alpha) (s : G) :
    characterModulationEquiv mu alpha chi f s = (chi s : ℂ) • f s := rfl

end HaarTwistedCore
