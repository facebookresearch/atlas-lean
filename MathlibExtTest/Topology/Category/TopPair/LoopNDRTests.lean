/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopPair.LoopNDR

/-!
# Consumers of the actual constant-loop NDR data

Use the public data and its raw path values to recognize the exact constant
loop, evaluate the actual deformation, and identify its controlled endpoint.
-/

open CategoryTheory Topology
open scoped unitInterval

noncomputable section

universe u

variable {X : PointedTopCat.{u}}
  (d : TopPair.StandardNDRData (PointedTopCat.pointedPair.obj X))

example (gamma : LoopSpace X.right (X.hom PUnit.unit)) :
    (d.loop (X := X)).control gamma = 0 ↔ gamma = Path.refl (X.hom PUnit.unit) := by
  refine ((d.loop (X := X)).control_eq_zero_iff gamma).trans ?_
  constructor
  · rintro ⟨p, hp⟩
    exact hp.symm
  · intro hgamma
    exact ⟨PUnit.unit, hgamma.symm⟩

example (s : unitInterval) (gamma : LoopSpace X.right (X.hom PUnit.unit))
    (t : unitInterval) :
    d.loopDeformation (s, gamma) t = d.deformation (s, gamma t) :=
  d.loop_deformation_apply s gamma t

example (s : unitInterval) :
    d.loopDeformation (s, Path.refl (X.hom PUnit.unit)) =
      Path.refl (X.hom PUnit.unit) := by
  apply Path.ext
  funext t
  rw [d.loop_deformation_apply]
  exact d.deformation.eq_fst s ⟨PUnit.unit, rfl⟩

example (gamma : LoopSpace X.right (X.hom PUnit.unit))
    (hgamma : (d.loop (X := X)).control gamma < 1) :
    d.loopEndpoint gamma = Path.refl (X.hom PUnit.unit) := by
  obtain ⟨p, hp⟩ := (d.loop (X := X)).endpoint_mem_range gamma hgamma
  exact hp.symm

#print axioms TopPair.StandardNDRData.loop
#print axioms TopPair.StandardNDRData.loop_control_norm
#print axioms TopPair.StandardNDRData.loop_deformation_apply
