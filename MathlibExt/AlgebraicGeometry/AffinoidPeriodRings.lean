/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Perfectoid.BDeRham
public import MathlibExt.RingTheory.CompleteHuberPairModels
public import MathlibExt.RingTheory.AdicCompletionMaps

/-!
# Actual affinoid Fontaine rings, filtration and completed theta

Coefficients use the actual integral plus ring of a genuine perfectoid
Huber pair. A_inf is its native Witt/inverse-Frobenius ring. B_dR^+ is
native kernel-theta completion after p-inversion, and its filtration uses
the actual quotient projections. Completed theta is the first projection
followed by the actual quotient-kernel map, so its unit square is fixed.

The completion/p-localization input identifies the ordinary completed
perfectoid-source primitives. It does not replace the geometric ring
with a freely named period algebra.

Sources: Mathlib Perfectoid/FontaineTheta.lean and BDeRham.lean
(Jiedong Jiang, Apache2.0); Scholze, arXiv:1205.3463v2,
Definitions6.1/6.2 and Section6; arXiv:1709.07343v4, Lemma3.14.
The completed theta adapter is original, using native quotient maps.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffinoidPeriodRings

open CategoryTheory
open MathlibExt.RingTheory.CompleteHuberPairModels

variable (p : ℕ) [Fact p.Prime] (P : PerfectoidPair p)

/-- Hypotheses on a perfectoid pair $P$ for a prime $p$, with ring $A$ (`P.ring`) and ring of
integral elements $A^+$ (`P.plus`): an instance asserts that $p$ is not a unit in $A^+$, that $A^+$
is $p$-adically complete and separated, that $A$ is the localization of $A^+$ away from $p$, and
that the Frobenius $x \mapsto x^p$ of $A^+/p$ is surjective. -/
class IntegralPeriodInput where
  [not_unit : Fact (¬ IsUnit (p : P.plus))]
  [complete : IsAdicComplete (Ideal.span {(p : P.plus)}) P.plus]
  [localization : IsLocalization.Away (p : P.plus) P.ring]
  frobenius : Function.Surjective (frobenius (ModP P.plus p) p)

attribute [instance] IntegralPeriodInput.not_unit IntegralPeriodInput.complete
  IntegralPeriodInput.localization

variable [D : IntegralPeriodInput p P]

/-- The actual Witt-vector ring of the integral inverse-Frobenius limit. -/
abbrev Ainf := WittVector p (PreTilt P.plus p)

/-- The native Fontaine map on these actual rings. -/
def theta : Ainf p P →+* P.plus := WittVector.fontaineTheta P.plus p

/-- Fontaine's map $\theta : A_{\mathrm{inf}} = W(A^{+\flat}) \to A^+$ is surjective, for a prime
$p$ and a perfectoid pair $P$ with ring of integral elements $A^+$ satisfying `IntegralPeriodInput`
(in particular, Frobenius is surjective on $A^+/p$). -/
theorem theta_surjective : Function.Surjective (theta p P) :=
  surjective_fontaineTheta D.frobenius

/-- The actual rational ring before kernel-theta completion. -/
abbrev PreDeRham := Localization.Away (p : Ainf p P)

/-- The actual p-inverted integral coefficient ring. -/
abbrev RationalPlus := Localization.Away (p : P.plus)

/-- The native p-inverted theta, whose actual kernel defines the completion. -/
def thetaInvertP : PreDeRham p P →+* RationalPlus p P :=
  fontaineThetaInvertP P.plus p

abbrev deRhamIdeal := RingHom.ker (thetaInvertP p P)

/-- The completed native period ring, with no replacement carrier. -/
abbrev DeRhamPlus := AdicCompletion (deRhamIdeal p P) (PreDeRham p P)

/-- Native localization of the completion at actual theta-kernel generators. -/
abbrev DeRham := BDeRham P.plus p

/-- The actual completion projection in every filtration degree. -/
def projection (n : ℕ) : DeRhamPlus p P →+*
    (PreDeRham p P ⧸ deRhamIdeal p P ^ n) :=
  (AdicCompletion.evalₐ (deRhamIdeal p P) n).toRingHom

/-- The filtration is the kernel of this fixed quotient projection. -/
def filtration (n : ℕ) : Ideal (DeRhamPlus p P) :=
  RingHom.ker (projection p P n)

/-- The actual completion unit. -/
def completionUnit : PreDeRham p P →+* DeRhamPlus p P := algebraMap _ _

/-- Theta on the completion, fixed by the first actual quotient projection. -/
def thetaPlus : DeRhamPlus p P →+* RationalPlus p P :=
  (Ideal.Quotient.lift (deRhamIdeal p P) (thetaInvertP p P)
    (fun _ h ↦ h)).comp
      (AdicCompletion.evalOneₐ (deRhamIdeal p P)).toRingHom

/-- The completed map extends exactly the native pre-completion theta. -/
theorem thetaPlus_unit :
    (thetaPlus p P).comp (completionUnit p P) = thetaInvertP p P := by
  unfold thetaPlus completionUnit
  rw [RingHom.comp_assoc]
  rw [AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
  ext a
  rfl

/-- The prescribed equivalence with the actual affinoid Tate ring. -/
def rationalPlusEquiv : RationalPlus p P ≃ₐ[P.plus] P.ring :=
  IsLocalization.algEquiv (Submonoid.powers (p : P.plus)) _ _

/-- Completed theta now has the actual geometric affinoid ring as target. -/
def thetaPlusToRing : DeRhamPlus p P →+* P.ring :=
  (rationalPlusEquiv p P).toRingHom.comp (thetaPlus p P)

/-- The real Witt-vector map into its native p-inverted completion. -/
def AinfToDeRham : Ainf p P →+* DeRhamPlus p P :=
  (completionUnit p P).comp (algebraMap _ _)

/-- Completed geometric theta evaluates a genuine Teichmuller class by sharp. -/
theorem thetaPlus_teichmuller (x : PreTilt P.plus p) :
    thetaPlusToRing p P (AinfToDeRham p P (WittVector.teichmuller p x)) =
      ((PreTilt.untilt x : P.plus) : P.ring) := by
  have h := RingHom.congr_fun (thetaPlus_unit p P)
    (algebraMap (Ainf p P) (PreDeRham p P) (WittVector.teichmuller p x))
  change (rationalPlusEquiv p P) ((thetaPlus p P)
    ((completionUnit p P)
      (algebraMap (Ainf p P) (PreDeRham p P) (WittVector.teichmuller p x)))) = _
  simp only [RingHom.comp_apply] at h
  rw [h]
  simp only [thetaInvertP, fontaineThetaInvertP, Localization.awayLift,
    IsLocalization.Away.lift_eq, RingHom.comp_apply,
    WittVector.fontaineTheta_teichmuller, AlgEquiv.commutes]
  rfl

/-- Actual theta-kernel powers define the filtration through the unit. -/
theorem completionUnit_mem_filtration {n : ℕ} {a : PreDeRham p P}
    (h : a ∈ deRhamIdeal p P ^ n) :
    completionUnit p P a ∈ filtration p P n := by
  change (AdicCompletion.evalₐ (deRhamIdeal p P) n)
    (AdicCompletion.of (deRhamIdeal p P) (PreDeRham p P) a) = 0
  rw [AdicCompletion.evalₐ_of]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr h

end MathlibExt.AlgebraicGeometry.AffinoidPeriodRings
