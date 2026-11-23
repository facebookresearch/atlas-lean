/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.Pi
public import MathlibExt.KTheory.Ring.Comparison.ScalarExtensionK0Coherence
public import MathlibExt.KTheory.Ring.Comparison.ScalarExtensionBaseChangeK0

/-!
# Finite-product K₀ scalar extension in independent coefficient universes

The original finite-product equivalence commutes with the actual canonical
scalar-extension maps. Source and target coefficient universes stay independent
at their native `RingK0` carriers. Reconstruction, identity, and three-universe
composition retain the same original product ring homomorphisms.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR uS uT w

namespace AlgebraicKTheory.RingK0

variable {ι : Type w} [Finite ι]
variable {R : ι → Type (max uR w)} {S : ι → Type (max uS w)}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]

/-- The entire original Pi equivalence commutes with canonical scalar extension,
with independently sized source and target coefficient families. -/
theorem piEquiv_scalarExtension_naturality (φ : ∀ i, R i →+* S i) :
    ((piEquiv.{uS, w} S).toRingHom.toAddMonoidHom).comp
        (FGProjectiveCat.scalarExtensionK0
          (RingHom.pi (fun i => (φ i).comp (Pi.evalRingHom R i)))) =
      (AddMonoidHom.pi (fun i => (FGProjectiveCat.scalarExtensionK0 (φ i)).comp
        (Pi.evalAddMonoidHom (fun i => RingK0 (R i)) i))).comp
          (piEquiv.{uR, w} R).toRingHom.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro a
  funext i
  change mapRingHom (Pi.evalRingHom S i)
      (FGProjectiveCat.scalarExtensionK0
        (RingHom.pi (fun j => (φ j).comp (Pi.evalRingHom R j))) a) =
    FGProjectiveCat.scalarExtensionK0 (φ i) (mapRingHom (Pi.evalRingHom R i) a)
  have h : (Pi.evalRingHom S i).comp
      (RingHom.pi (fun j => (φ j).comp (Pi.evalRingHom R j))) =
        (φ i).comp (Pi.evalRingHom R i) := rfl
  have hk := congrArg (fun f => FGProjectiveCat.scalarExtensionK0 f) h
  rw [FGProjectiveCat.scalarExtensionK0_comp, FGProjectiveCat.scalarExtensionK0_comp] at hk
  have hs := FGProjectiveCat.scalarExtensionK0_eq_mapRingHom (Pi.evalRingHom S i)
  have hr := FGProjectiveCat.scalarExtensionK0_eq_mapRingHom (Pi.evalRingHom R i)
  rw [hs, hr] at hk
  exact DFunLike.congr_fun hk a

/-- Every component retains the original evaluation and coefficient-extension maps. -/
theorem piEquiv_scalarExtension_apply (φ : ∀ i, R i →+* S i)
    (a : RingK0 (∀ i, R i)) (i : ι) :
    piEquiv.{uS, w} S
        (FGProjectiveCat.scalarExtensionK0
          (RingHom.pi (fun j => (φ j).comp (Pi.evalRingHom R j))) a) i =
      FGProjectiveCat.scalarExtensionK0 (φ i) (piEquiv.{uR, w} R a i) :=
  congrFun (DFunLike.congr_fun (piEquiv_scalarExtension_naturality φ) a) i

/-- The original Pi inverse reconstructs the same class after independent-universe
scalar extension of every supplied component. -/
theorem piEquiv_scalarExtension_symm (φ : ∀ i, R i →+* S i)
    (a : ∀ i, RingK0 (R i)) :
    FGProjectiveCat.scalarExtensionK0
        (RingHom.pi (fun i => (φ i).comp (Pi.evalRingHom R i)))
          ((piEquiv.{uR, w} R).symm a) =
      (piEquiv.{uS, w} S).symm (fun i => FGProjectiveCat.scalarExtensionK0 (φ i) (a i)) := by
  apply (piEquiv S).injective
  rw [(piEquiv S).apply_symm_apply]
  have h := DFunLike.congr_fun (piEquiv_scalarExtension_naturality φ) ((piEquiv R).symm a)
  change piEquiv S
      (FGProjectiveCat.scalarExtensionK0
        (RingHom.pi (fun i => (φ i).comp (Pi.evalRingHom R i))) ((piEquiv R).symm a)) =
    (fun i => FGProjectiveCat.scalarExtensionK0 (φ i) (piEquiv R ((piEquiv R).symm a) i)) at h
  rw [(piEquiv R).apply_symm_apply] at h
  exact h

omit [Finite ι] in
/-- The actual coordinatewise identity ring map induces the whole identity K₀ map. -/
theorem piScalarExtension_id :
    FGProjectiveCat.scalarExtensionK0
        (RingHom.pi (fun i => (RingHom.id (R i)).comp (Pi.evalRingHom R i))) =
      AddMonoidHom.id (RingK0 (∀ i, R i)) := by
  have h : RingHom.pi (fun i => (RingHom.id (R i)).comp (Pi.evalRingHom R i)) =
      RingHom.id (∀ i, R i) := rfl
  rw [h]
  exact FGProjectiveCat.scalarExtensionK0_id (∀ i, R i)

variable {T : ι → Type (max uT w)} [∀ i, CommRing (T i)]

omit [Finite ι] in
/-- The original product ring maps and native K₀ maps compose across three
independent coefficient universes. -/
theorem piScalarExtension_comp (φ : ∀ i, R i →+* S i) (ψ : ∀ i, S i →+* T i) :
    FGProjectiveCat.scalarExtensionK0
        (RingHom.pi (fun i => ((ψ i).comp (φ i)).comp (Pi.evalRingHom R i))) =
      (FGProjectiveCat.scalarExtensionK0
        (RingHom.pi (fun i => (ψ i).comp (Pi.evalRingHom S i)))).comp
          (FGProjectiveCat.scalarExtensionK0
            (RingHom.pi (fun i => (φ i).comp (Pi.evalRingHom R i)))) := by
  have h : (RingHom.pi (fun i => (ψ i).comp (Pi.evalRingHom S i))).comp
      (RingHom.pi (fun i => (φ i).comp (Pi.evalRingHom R i))) =
        RingHom.pi (fun i => ((ψ i).comp (φ i)).comp (Pi.evalRingHom R i)) := rfl
  have hk := FGProjectiveCat.scalarExtensionK0_comp
    (RingHom.pi (fun i => (φ i).comp (Pi.evalRingHom R i)))
    (RingHom.pi (fun i => (ψ i).comp (Pi.evalRingHom S i)))
  rw [h] at hk
  exact hk

/-- Reconstruction and both actual scalar-extension steps retain all three
native coefficient universes and the original factor maps. -/
theorem piEquiv_scalarExtension_symm_comp (φ : ∀ i, R i →+* S i)
    (ψ : ∀ i, S i →+* T i) (a : ∀ i, RingK0 (R i)) :
    FGProjectiveCat.scalarExtensionK0
        (RingHom.pi (fun i => (ψ i).comp (Pi.evalRingHom S i)))
          (FGProjectiveCat.scalarExtensionK0
            (RingHom.pi (fun i => (φ i).comp (Pi.evalRingHom R i)))
              ((piEquiv.{uR, w} R).symm a)) =
      (piEquiv.{uT, w} T).symm (fun i =>
        FGProjectiveCat.scalarExtensionK0 (ψ i)
          (FGProjectiveCat.scalarExtensionK0 (φ i) (a i))) := by
  rw [piEquiv_scalarExtension_symm φ a]
  exact piEquiv_scalarExtension_symm ψ _

end AlgebraicKTheory.RingK0

end
