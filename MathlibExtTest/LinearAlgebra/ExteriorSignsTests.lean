/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Alternating.HeadAntisymmetrization
import MathlibExt.LinearAlgebra.ExteriorAlgebra.DerivationPure
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Ordered integer tuples in alternatization and exterior derivations

Coordinate-product forms on integer vectors are not symmetric. The ordered
tuples below have nonzero determinants, so deleting a tail in the wrong order or
using the wrong head sign changes the value. The exterior identity derivation
also distinguishes the two orders of the inherited two-vector tail.
-/

noncomputable section

open scoped BigOperators

namespace MathlibExtTest.ExteriorSigns

private abbrev M2 := Fin 2 → ℤ
private abbrev M3 := Fin 3 → ℤ

private def coordinateForm (n : ℕ) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Fin n → ℤ) ℤ :=
  (MultilinearMap.mkPiRing ℤ (Fin n) (1 : ℤ)).compLinearMap
    (fun i => LinearMap.proj i)

private def ordered2 : Fin 2 → M2 := ![![2, 3], ![5, 7]]
private def reversed3 : Fin 3 → M3 := ![![0, 0, 5], ![0, 3, 0], ![2, 0, 0]]

example :
    (coordinateForm 2).curryLeft.uncurryLeft.alternatization ordered2 = (-1 : ℤ) := by
  rw [MultilinearMap.alternatization_uncurryLeft]
  norm_num [AlternatingMap.alternatizeUncurryFin_apply,
    MultilinearMap.alternatizeTail, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, coordinateForm, ordered2,
    Fin.sum_univ_two, Fin.removeNth]

private def twoHeads :
    M3 →ₗ[ℤ] M3 →ₗ[ℤ] MultilinearMap (RingHom.id ℤ) (fun _ : Fin 1 => M3) ℤ :=
  ((multilinearCurryLeftEquiv (RingHom.id ℤ)
    (fun _ : Fin 2 => M3) ℤ).toLinearMap).comp (coordinateForm 3).curryLeft

example :
    (LinearMap.uncurryLeft
      (((multilinearCurryLeftEquiv (RingHom.id ℤ)
        (fun _ : Fin 2 => M3) ℤ).symm.toLinearMap).comp twoHeads)).alternatization
      reversed3 = (-30 : ℤ) := by
  rw [MultilinearMap.alternatization_uncurryLeft_twice]
  norm_num [AlternatingMap.alternatizeUncurryFin_apply,
    AlternatingMap.alternatizeUncurryFinLM, MultilinearMap.alternatizeTailLinearMap,
    MultilinearMap.alternatizeTail, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, twoHeads, coordinateForm, reversed3,
    Fin.sum_univ_three, Fin.sum_univ_two, Fin.removeNth]

example :
    ExteriorAlgebra.derivation ℤ M2 (LinearMap.id : Module.End ℤ M2)
        (ExteriorAlgebra.ιMulti ℤ 2 ordered2) =
      ExteriorAlgebra.ιMulti ℤ 2 ordered2 -
        ExteriorAlgebra.ιMulti ℤ 2 ![ordered2 1, ordered2 0] := by
  rw [ExteriorAlgebra.derivation_ιMulti_eq_sum_vecCons]
  simp [Fin.sum_univ_two, Fin.removeNth, ordered2, sub_eq_add_neg]

example :
    ((ExteriorAlgebra.derivationLieHom ℤ M2).toLinearMap
      (LinearMap.id : Module.End ℤ M2)) (ExteriorAlgebra.ι ℤ (M := M2) (ordered2 0)) =
        ExteriorAlgebra.ι ℤ (M := M2) (ordered2 0) := by
  rw [ExteriorAlgebra.derivationLieHom_toLinearMap, ExteriorAlgebra.derivation_ι]
  rfl

end MathlibExtTest.ExteriorSigns
