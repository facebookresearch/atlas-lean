/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Perfectoid.BDeRham
public import MathlibExt.AlgebraicGeometry.HodgeTateComparison
public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingGalois

/-!
# The filtration of `B_dR^+` and `Fil^j D_dR` of `H¹`

Mathlib's `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p` is the `(ker θ)`-adic completion of
`W(𝓞_ℂ_p^♭)[1/p]`. Its filtration `Fil^j B_dR^+` is the kernel of the projection to
`W(𝓞_ℂ_p^♭)[1/p] ⧸ (ker θ)^j` (`fil`). The Galois group `Gal(\bar{ℚ}_p/ℚ_p)` acts on `B_dR^+`,
`ℚ_p`-linearly, by `PadicComplexInt.galoisBDeRhamPlus`, and `B_dR^+` is a `ℚ_p`-algebra by
`PadicComplexInt.instAlgebraPadicBDeRhamPlus`. For a scheme `A` over a subfield `F` of
`\bar{ℚ}_p` and `V = H¹_ét(A_{\bar{ℚ}_p}, ℚ_p)`, `filDeRham` is
`Fil^j D_dR(V) = (Fil^j B_dR^+ ⊗ V)^{G_F}` for `j ≥ 0`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open HodgeTateComparison GeometricAdicGaloisOperators AdicLinearFunctoriality
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

section Completion

/-- The kernel of Fontaine's map
$\theta \colon W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p] \to \mathcal{O}_{\mathbb{C}_p}[1/p]$. -/
abbrev thetaKer : Ideal (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) :=
  RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)

/-- The projection
$B_{\mathrm{dR}}^+ \to W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]/(\ker\theta)^n$. -/
def evalBdR (n : ℕ) : BDeRhamPlus 𝓞_ℂ_[p] p →+*
    Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) ⧸ thetaKer p ^ n :=
  (AdicCompletion.evalₐ (thetaKer p) n).toRingHom

/-- The filtration $\operatorname{Fil}^j B_{\mathrm{dR}}^+$: the kernel of the projection to
$W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]/(\ker\theta)^j$. -/
def fil (j : ℕ) : Ideal (BDeRhamPlus 𝓞_ℂ_[p] p) := RingHom.ker (evalBdR p j)

end Completion

section Cohomology

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (A : Over (Spec (CommRingCat.of F)))

/-- $H^1_{\mathrm{et}}(A_{\overline{\mathbb{Q}}_p}, \mathbb{Q}_p)$ for a scheme $A$ over $F$: the
first cohomology of the pro-étale sheaf of continuous $\mathbb{Q}_p$-valued functions on the base
change $A_{\overline{\mathbb{Q}}_p}$. -/
abbrev H1 : Type 1 := AdicCohomology p (geometricFibre A (PadicAlgCl p)) 1

/-- The action of $\sigma \in \operatorname{Gal}(\overline{\mathbb{Q}}_p/F)$ on
$H^1_{\mathrm{et}}(A_{\overline{\mathbb{Q}}_p}, \mathbb{Q}_p)$: inverse image along
$\mathrm{id}_A \times \operatorname{Spec} \sigma$. -/
def h1Galois (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) : H1 p F A →ₗ[ℚ_[p]] H1 p F A :=
  continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p)
    (galoisSchemeOperator A (PadicAlgCl p) σ) 1

/-- $\operatorname{Fil}^j D_{\mathrm{dR}}(V) =
(\operatorname{Fil}^j B_{\mathrm{dR}}^+ \otimes_{\mathbb{Q}_p} V)^{G_F}$ for
$V = H^1_{\mathrm{et}}(A_{\overline{\mathbb{Q}}_p}, \mathbb{Q}_p)$ and $j \ge 0$: the elements of
the image of $\operatorname{Fil}^j B_{\mathrm{dR}}^+ \otimes_{\mathbb{Q}_p} V$ in
$B_{\mathrm{dR}}^+ \otimes_{\mathbb{Q}_p} V$ that every $\sigma \in G_F$ fixes, where $\sigma$
acts on $B_{\mathrm{dR}}^+$ by `PadicComplexInt.galoisBDeRhamPlus` and on $V$ by `h1Galois`. -/
def filDeRham (j : ℕ) : Submodule ℚ_[p] (BDeRhamPlus 𝓞_ℂ_[p] p ⊗[ℚ_[p]] H1 p F A) :=
  LinearMap.range (TensorProduct.map ((fil p j).restrictScalars ℚ_[p]).subtype
      (LinearMap.id : H1 p F A →ₗ[ℚ_[p]] H1 p F A)) ⊓
    ⨅ σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p,
      LinearMap.eqLocus
        (TensorProduct.map
          (PadicComplexInt.galoisBDeRhamPlus p (σ.restrictScalars ℚ_[p])).toLinearMap
          (h1Galois p F A σ)) LinearMap.id

end Cohomology

end MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison
