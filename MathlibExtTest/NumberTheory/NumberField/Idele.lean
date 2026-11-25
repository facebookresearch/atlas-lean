/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Idele

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

section TestIntRational

example : CommGroup (TopologicalIdeleGroup ℤ ℚ) := inferInstance
example : TopologicalSpace (TopologicalIdeleGroup ℤ ℚ) := inferInstance
example : IsTopologicalGroup (TopologicalIdeleGroup ℤ ℚ) := inferInstance

example : CommGroup (FiniteIdeleGroup ℤ ℚ) := inferInstance
example : TopologicalSpace (FiniteIdeleGroup ℤ ℚ) := inferInstance
example : IsTopologicalGroup (FiniteIdeleGroup ℤ ℚ) := inferInstance

example : CommGroup (InfiniteIdeleGroup ℚ) := inferInstance
example : TopologicalSpace (InfiniteIdeleGroup ℚ) := inferInstance
example : IsTopologicalGroup (InfiniteIdeleGroup ℚ) := inferInstance

example : TopologicalSpace (TopologicalIdeleClassGroup ℤ ℚ) := inferInstance
example : IsTopologicalGroup (TopologicalIdeleClassGroup ℤ ℚ) := inferInstance

example : TopologicalIdeleGroup.principalEmbedding ℤ ℚ 1 = 1 := by
  simp

example : Function.Injective (TopologicalIdeleGroup.principalEmbedding ℤ ℚ) :=
  TopologicalIdeleGroup.principalEmbedding_injective ℤ ℚ

example : (QuotientGroup.mk (s := TopologicalIdeleGroup.principalIdeles ℤ ℚ)
    (TopologicalIdeleGroup.principalEmbedding ℤ ℚ 1) :
      TopologicalIdeleClassGroup ℤ ℚ) = 1 := by
  simp

def testAdeleUnitsToIdele : (AdeleRing ℤ ℚ)ˣ →* TopologicalIdeleGroup ℤ ℚ :=
  (TopologicalIdeleGroup.unitsEquiv ℤ ℚ).toMonoidHom

def testIdeleToAdeleUnits : TopologicalIdeleGroup ℤ ℚ →* (AdeleRing ℤ ℚ)ˣ :=
  (TopologicalIdeleGroup.unitsEquiv ℤ ℚ).symm.toMonoidHom

example (u : (AdeleRing ℤ ℚ)ˣ) :
    testIdeleToAdeleUnits (testAdeleUnitsToIdele u) = u := by
  simp [testAdeleUnitsToIdele, testIdeleToAdeleUnits]

example (x : TopologicalIdeleGroup ℤ ℚ) :
    testAdeleUnitsToIdele (testIdeleToAdeleUnits x) = x := by
  simp [testAdeleUnitsToIdele, testIdeleToAdeleUnits]

example (x : ℚˣ) (v : InfinitePlace ℚ) :
    (TopologicalIdeleGroup.principalEmbedding ℤ ℚ x).1 v =
      Units.map (algebraMap ℚ v.Completion).toMonoidHom x := by
  rw [TopologicalIdeleGroup.principalEmbedding_fst,
    TopologicalIdeleGroup.infinitePrincipalEmbedding_apply]

example (x : ℚˣ) (v : HeightOneSpectrum ℤ) :
    (TopologicalIdeleGroup.principalEmbedding ℤ ℚ x).2 v =
      Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom x := by
  rw [TopologicalIdeleGroup.principalEmbedding_snd,
    TopologicalIdeleGroup.finitePrincipalEmbedding_apply]

end TestIntRational
