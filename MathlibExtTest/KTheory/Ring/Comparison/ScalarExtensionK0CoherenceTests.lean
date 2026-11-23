/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.ScalarExtensionK0Coherence
public import MathlibExt.KTheory.Ring.Comparison.ScalarExtensionBaseChangeK0
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Clients of scalar extension in independent universes

These clients keep the original ring K₀ carriers. Evaluation of an ordinary
continuous-function ring lands in the smaller coefficient-ring universe.
Its constant section and its compatibility with actual precomposition use
the whole scalar-extension maps, without a Noetherian hypothesis.
-/

public section
noncomputable section

open AlgebraicKTheory FGProjectiveCat

universe uR uS uT uU uX uY u

section Associative

variable {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
  [Ring R] [Ring S] [Ring T] [Ring U]

example (f : R →+* S) (g : S →+* T) (h : T →+* U) (a : RingK0 R) :
    scalarExtensionK0 ((h.comp g).comp f) a =
      scalarExtensionK0 h (scalarExtensionK0 g (scalarExtensionK0 f a)) := by
  rw [scalarExtensionK0_comp, AddMonoidHom.comp_apply,
    scalarExtensionK0_comp, AddMonoidHom.comp_apply]

example (f : R →+* S) :
    scalarExtensionK0 f (K0.mk (FGProjectiveCat.of (R := R) R)) =
      K0.mk (FGProjectiveCat.of (R := S) S) :=
  scalarExtensionK0_regular f

end Associative

section ContinuousFunctions

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
  {R : Type uR} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

example (x : X) (a : RingK0 R) :
    scalarExtensionK0 (ContinuousMap.evalAlgHom R R x).toRingHom
      (scalarExtensionK0 (ContinuousMap.C : R →+* C(X, R)) a) = a := by
  let ev := (ContinuousMap.evalAlgHom R R x).toRingHom
  let const := (ContinuousMap.C : R →+* C(X, R))
  have h : ev.comp const = RingHom.id R := by
    ext r
    rfl
  change ((scalarExtensionK0 ev).comp (scalarExtensionK0 const)) a = a
  rw [← scalarExtensionK0_comp, h, scalarExtensionK0_id, AddMonoidHom.id_apply]

example (f : C(X, Y)) (x : X) (a : RingK0 C(Y, R)) :
    scalarExtensionK0 (ContinuousMap.evalAlgHom R R x).toRingHom
        (scalarExtensionK0 (ContinuousMap.compRightAlgHom R R f).toRingHom a) =
      scalarExtensionK0 (ContinuousMap.evalAlgHom R R (f x)).toRingHom a := by
  let ev := (ContinuousMap.evalAlgHom R R x).toRingHom
  let pull := (ContinuousMap.compRightAlgHom R R f).toRingHom
  let evPull := (ContinuousMap.evalAlgHom R R (f x)).toRingHom
  have h : ev.comp pull = evPull := by
    ext c
    rfl
  change ((scalarExtensionK0 ev).comp (scalarExtensionK0 pull)) a =
    scalarExtensionK0 evPull a
  rw [← scalarExtensionK0_comp, h]

end ContinuousFunctions

section Commutative

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

example (f : R →+* S) (g : S →+* T) :
    (scalarExtensionK0 g).comp (scalarExtensionK0 f) =
      ((RingK0.mapRingHom g).comp (RingK0.mapRingHom f)).toAddMonoidHom := by
  rw [scalarExtensionK0_eq_mapRingHom, scalarExtensionK0_eq_mapRingHom]
  rfl

end Commutative

#print axioms FGProjectiveCat.scalarExtensionK0_id
#print axioms FGProjectiveCat.scalarExtensionK0_comp
#print axioms FGProjectiveCat.scalarExtensionK0_regular

end
