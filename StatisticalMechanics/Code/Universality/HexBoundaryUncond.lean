/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Code.Universality.HexContourDecomp
import Code.Universality.HexVertexBoundConcrete

namespace StatMech.Universality

open Complex
open scoped BigOperators











noncomputable def hexUncondMid (a : ℂ) (h0 : ℤ) : Fin 3 → ℂ
  | 0 => hexConcreteV a h0 + hexConcreteDu a h0
  | 1 => hexConcreteV a h0 + hexOmega * hexConcreteDu a h0
  | 2 => hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0



noncomputable def hexUncondObs (a : ℂ) (h0 : ℤ) (z : ℂ) : ℂ :=
  parafObservable (hexVBCRegion a h0).inRegion a h0 z (5/8) hexChi






noncomputable def hexUncondDomain (a : ℂ) (h0 : ℤ) : HexDomain (Fin 1) where
  interiorVertices := {0}
  pos := fun _ => hexConcreteV a h0
  mid := fun _ => hexUncondMid a h0
  obs := hexUncondObs a h0
  relation := by
    intro v _
    
    rw [Fin.sum_univ_three]
    change (hexUncondMid a h0 0 - hexConcreteV a h0) * hexUncondObs a h0 (hexUncondMid a h0 0)
        + (hexUncondMid a h0 1 - hexConcreteV a h0) * hexUncondObs a h0 (hexUncondMid a h0 1)
        + (hexUncondMid a h0 2 - hexConcreteV a h0) * hexUncondObs a h0 (hexUncondMid a h0 2) = 0
    unfold hexUncondMid hexUncondObs
    exact hexVBC_vertex_relation_unconditional a h0



@[simp]
theorem hexUncondDomain_interiorVertices (a : ℂ) (h0 : ℤ) :
    (hexUncondDomain a h0).interiorVertices = {0} := rfl













def hexUncondPairing (a : ℂ) (h0 : ℤ) : (hexUncondDomain a h0).InteriorPairing where
  interior := ∅
  pair := id
  pair_mem := by intro e he; simp at he
  pair_invol := by intro e he; simp at he
  pair_ne := by intro e he; simp at he
  cancel := by intro e he; simp at he


theorem hexUncond_interior_sub (a : ℂ) (h0 : ℤ) :
    (hexUncondPairing a h0).interior ⊆ (hexUncondDomain a h0).incidences := by
  intro e he; simp [hexUncondPairing] at he



















theorem hexUncond_raw_eq_zero (a : ℂ) (h0 : ℤ) :
    (hexUncondDomain a h0).boundarySum (hexUncondPairing a h0) = 0 :=
  (hexUncondDomain a h0).hexBoundaryRaw (hexUncondPairing a h0) (hexUncond_interior_sub a h0)





















theorem hexBoundary_identity_uncond (a : ℂ) (h0 : ℤ) (lam tau ups Fa : ℝ)
    (hFa : Fa = 1)
    (hdecomp : (hexUncondDomain a h0).boundarySum (hexUncondPairing a h0)
      = Complex.I * ((hexBdryCl * lam + hexBdryCt * tau + ups : ℝ) - (Fa : ℝ))) :
    hexBdryCl * lam + hexBdryCt * tau + ups = 1 :=
  hexBoundary_of_decomp lam tau ups Fa
    ((hexUncondDomain a h0).boundarySum (hexUncondPairing a h0))
    (hexUncond_raw_eq_zero a h0) hFa hdecomp








theorem hexBoundary_identity_uncond_scales (a : ℕ → ℂ) (h0 : ℕ → ℤ)
    (lam tau ups Fa : ℕ → ℝ)
    (hFa : ∀ v, 1 ≤ v → Fa v = 1)
    (hdecomp : ∀ v, 1 ≤ v →
      (hexUncondDomain (a v) (h0 v)).boundarySum (hexUncondPairing (a v) (h0 v))
        = Complex.I * ((hexBdryCl * lam v + hexBdryCt * tau v + ups v : ℝ) - (Fa v : ℝ))) :
    ∀ v, 1 ≤ v → hexBdryCl * lam v + hexBdryCt * tau v + ups v = 1 := by
  intro v hv
  exact hexBoundary_identity_uncond (a v) (h0 v) (lam v) (tau v) (ups v) (Fa v)
    (hFa v hv) (hdecomp v hv)











theorem hexBoundary_identity_uncond_via_decomp (a : ℂ) (h0 : ℤ)
    (B : HexBoundaryDecomp (hexUncondDomain a h0) (hexUncondPairing a h0))
    (hFa : B.Fa = 1) :
    hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups = 1 := by
  refine hexBoundary_identity_uncond a h0 B.lam (B.taup + B.taum) B.ups B.Fa hFa ?_
  have h := B.boundarySum_eq
  simpa using h

end StatMech.Universality
