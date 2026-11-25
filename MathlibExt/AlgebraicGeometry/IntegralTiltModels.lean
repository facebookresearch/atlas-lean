/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Perfectoid.Untilt
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Constructions
public import MathlibExt.AlgebraicGeometry.PerfectoidLocalModels

/-!
# Canonical integral-tilt model and all-rank point comparison contracts

The integral ring is the actual native inverse Frobenius limit A°/(p).
Its topology is the coefficient initial topology. The Tate ring is its
actual localization at the compatible pseudouniformizer, with the final
topology of the integral denominator charts. The plus-ring criterion is
membership of the actual sharp in the original plus ring.

This fixes the local tilt model supplied by completed Tau sources;
no new raw perfectoid or local tilt-ring constructor is requested.
The separate all-rank homeomorphism contract is normalized on every
integral numerator pair, so it cannot be an arbitrary homeomorphism.
It compares valuations, never a ringed-space isomorphism across characteristics.

Sources: Scholze, arXiv:1709.07343v4, Definition 3.1, Lemma 3.11 and
Theorem 3.12; arXiv:1111.4914v1, Theorem 6.3.
TauCetiProject/TauCeti revision62bbc0596dc3539d488232e4e924a338548ea0a9,
`RingTheory/Perfectoid/UniformTilt/{Plus,Pair,Tate}.lean` and
`PseudoUniformizerRoots/Basic.lean` (Apache2.0). Source-normalized model
inputs below identify the completed local ring constructions and their
canonical topology adapter; they are not claimed new proofs of tilting.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntegralTiltModels

open CategoryTheory TopologicalSpace Topology
open MathlibExt.RingTheory.CompleteHuberPairModels

variable (p : ℕ) [Fact p.Prime] (P : PerfectoidPair p)

/-- The compatible root and completion input of the completed local source. -/
class IntegralInput where
  [not_unit : Fact (¬ IsUnit (p : P.powerbounded))]
  [complete : IsAdicComplete (Ideal.span {(p : P.powerbounded)}) P.powerbounded]
  roots : ℕ → P.powerbounded
  compatible : ∀ n, roots (n + 1) ^ p = roots n
  root_zero_unit : IsUnit (roots 0 : P.ring)
  root_zero_nilpotent : IsTopologicallyNilpotent (roots 0 : P.ring)

attribute [instance] IntegralInput.not_unit IntegralInput.complete

/-- The actual native inverse-limit ring. -/
abbrev IntegralRing := PreTilt P.powerbounded p

variable [D : IntegralInput p P]

/-- The actual compatible pseudouniformizer in the inverse-limit ring. -/
def rootElement : IntegralRing p P :=
  ⟨fun n ↦ Ideal.Quotient.mk (Ideal.span {(p : P.powerbounded)}) (D.roots n),
    fun n ↦ by rw [← map_pow, D.compatible]⟩

/-- Coefficient topology inherited from the actual quotient ring. -/
@[instance_reducible] def integralTopology :
    TopologicalSpace (IntegralRing p P) :=
  TopologicalSpace.induced
    (fun x : IntegralRing p P ↦
      fun n : ℕ ↦ PreTilt.coeff n x)
    inferInstance

/-- The actual localization at the compatible root pseudouniformizer. -/
abbrev TateRing :=
  Localization.Away (rootElement p P (D := D))

/-- The literal integral denominator charts defining its final topology. -/
def denominatorChart :
    (Σ _ : ℕ, IntegralRing p P) → TateRing p P (D := D) :=
  fun x ↦ algebraMap (IntegralRing p P) (TateRing p P (D := D)) x.2 *
    IsLocalization.Away.invSelf (rootElement p P (D := D)) ^ x.1

/-- No freely chosen tilt topology: all denominator charts generate it. -/
@[instance_reducible] def tateTopology :
    TopologicalSpace (TateRing p P (D := D)) :=
  letI := integralTopology p P (D := D)
  TopologicalSpace.coinduced (denominatorChart p P (D := D)) inferInstance

/-- The actual multiplicative sharp, included in the original Tate ring. -/
def sharp (a : IntegralRing p P) : P.ring :=
  (PreTilt.untilt a : P.powerbounded)

@[simp] theorem sharp_zero : sharp p P (D := D) 0 = 0 := by
  change ((Perfection.teichmuller p (Ideal.span {(p : P.powerbounded)}) 0 :
    P.powerbounded) : P.ring) = 0
  rw [Perfection.teichmuller_zero]
  rfl

@[simp] theorem sharp_one : sharp p P (D := D) 1 = 1 := by
  change ((PreTilt.untilt (1 : IntegralRing p P) : P.powerbounded) : P.ring) = 1
  rw [map_one]
  rfl

private theorem roots_pow (n : ℕ) : D.roots n ^ p ^ n = D.roots 0 := by
  induction n with
  | zero => simp
  | succ n hn => rw [Nat.pow_succ', pow_mul, D.compatible, hn]

/-- The compatible denominator has the prescribed actual sharp. -/
theorem sharp_root :
    sharp p P (D := D) (rootElement p P (D := D)) = (D.roots 0 : P.ring) := by
  change ((Perfection.teichmuller p (Ideal.span {(p : P.powerbounded)})
    (rootElement p P (D := D)) : P.powerbounded) : P.ring) = _
  have h := Perfection.teichmuller_spec (p := p)
    (I := Ideal.span {(p : P.powerbounded)})
    (x := rootElement p P (D := D)) (y := D.roots 0)
    (fun n ↦ ⟨D.roots n, rfl, by rw [roots_pow p P]; rfl⟩)
  rw [h]

/-- The completed local tilt source, identified with this fixed presentation. -/
structure TiltModel where
  pair : CharPPerfectoidPair p
  ringEquiv : TateRing p P (D := D) ≃+* pair.ring
  continuous : @Continuous _ _ (tateTopology p P (D := D)) _ ringEquiv
  continuous_inverse : @Continuous _ _ _ (tateTopology p P (D := D)) ringEquiv.symm
  plus : ∀ x : pair.ring, x ∈ pair.plus ↔
    ∃ a : IntegralRing p P,
      ringEquiv (algebraMap (IntegralRing p P) (TateRing p P (D := D)) a) = x ∧
        sharp p P (D := D) a ∈ P.plus

/-- The prescribed integral-ring map of the actual local model. -/
def TiltModel.integralMap (M : TiltModel p P (D := D)) :
    IntegralRing p P →+* M.pair.ring :=
  M.ringEquiv.toRingHom.comp (algebraMap _ _)

/-- A point comparison fixed on all integral numerator pairs. -/
structure TiltingPoints (M : TiltModel p P (D := D)) where
  homeomorph : P.toHuberPair.Space ≃ₜ M.pair.toHuberPair.Space
  comparison : ∀ (v : P.toHuberPair.Space) (a b : IntegralRing p P),
    (homeomorph v).1.relation.vle
      (TiltModel.integralMap p P M a) (TiltModel.integralMap p P M b) ↔
      v.1.relation.vle (sharp p P (D := D) a) (sharp p P (D := D) b)

/-- The exact local rational condition before changing characteristic. -/
def sharpRational (T : Finset (IntegralRing p P))
    (s : IntegralRing p P) : Set P.toHuberPair.Space :=
  {v | ¬ v.1.relation.vle (sharp p P (D := D) s) 0 ∧
    ∀ a ∈ T, v.1.relation.vle (sharp p P (D := D) a) (sharp p P (D := D) s)}

/-- The corresponding real rational condition in the actual tilt ring. -/
def tiltRational (M : TiltModel p P (D := D))
    (T : Finset (IntegralRing p P)) (s : IntegralRing p P) :
    Set M.pair.toHuberPair.Space :=
  {v | ¬ v.1.relation.vle (TiltModel.integralMap p P M s) 0 ∧
    ∀ a ∈ T, v.1.relation.vle (TiltModel.integralMap p P M a)
      (TiltModel.integralMap p P M s)}

/-- The normalized point comparison transports these actual rational opens. -/
theorem rational_preimage (M : TiltModel p P (D := D))
    (E : TiltingPoints p P M) (T : Finset (IntegralRing p P))
    (s : IntegralRing p P) :
    E.homeomorph ⁻¹' tiltRational p P M T s =
      sharpRational p P T s := by
  ext v
  have h0 := E.comparison v s 0
  simp only [map_zero, sharp_zero] at h0
  simp only [Set.mem_preimage, tiltRational, sharpRational,
    Set.mem_ofPred_eq, h0, E.comparison]

end MathlibExt.AlgebraicGeometry.IntegralTiltModels
