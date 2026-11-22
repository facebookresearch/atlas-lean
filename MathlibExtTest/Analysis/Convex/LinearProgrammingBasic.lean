/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.LinearProgrammingBasic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Tests for basic points of standard-form polyhedra (`LPBasic`): attained optima
(T-attained, T-unique), the empty and `Fin 0` cases (T-empty, T-iota-empty), degenerate and
redundant constraints (T-degenerate, T-redundant), unbounded objectives (T-unbounded), the zero
functional (T-constant), and a general real module `E` (T-general-E). Each fixture checks
concrete arithmetic independently and applies the public exports `IsBasicPt`,
`exists_basic_optimal` and `finite_basic`. -/

open MathlibExt.Analysis.Convex.LPBasic
open scoped Matrix

namespace MathlibExtTest.Analysis.Convex.LinearProgrammingBasic

/-! ### T-attained (FX01): `L = [[1, 1, 1]]`, `c = (1)`, `φ = (1, 1, 2)` -/

/-- T-attained constraint map. -/
private noncomputable def attL : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
  (Matrix.of ![![1, 1, 1]]).mulVecLin

private theorem attL_apply (z : Fin 3 → ℝ) : attL z = ![z 0 + z 1 + z 2] := by
  funext j
  fin_cases j
  simp [attL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- T-attained objective `φ = (1, 1, 2)`. -/
private noncomputable def attPhi : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun z := z 0 + z 1 + 2 * z 2
  map_add' x y := by
    show (x + y) 0 + (x + y) 1 + 2 * (x + y) 2
      = (x 0 + x 1 + 2 * x 2) + (y 0 + y 1 + 2 * y 2)
    simp [Pi.add_apply]; ring
  map_smul' a x := by
    show (a • x) 0 + (a • x) 1 + 2 * (a • x) 2 = a • (x 0 + x 1 + 2 * x 2)
    simp [Pi.smul_apply, smul_eq_mul]; ring

private theorem attPhi_apply (z : Fin 3 → ℝ) : attPhi z = z 0 + z 1 + 2 * z 2 := rfl

/-- `(1/2, 1/2, 0)` is feasible. -/
private theorem att_z_nonneg : 0 ≤ ![1 / 2, 1 / 2, (0 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem att_z_eq : attL ![1 / 2, 1 / 2, (0 : ℝ)] = ![1] := by
  rw [attL_apply]
  funext j
  fin_cases j
  simp
  norm_num

/-- `(1/2, 1/2, 0)` has value 1 and minimizes `φ`. -/
private theorem att_phi_val : attPhi ![1 / 2, 1 / 2, (0 : ℝ)] = 1 := by
  rw [attPhi_apply]
  simp
  norm_num

private theorem att_opt : ∀ z' : Fin 3 → ℝ, 0 ≤ z' → attL z' = ![1] →
    attPhi ![1 / 2, 1 / 2, (0 : ℝ)] ≤ attPhi z' := by
  intro z' hz' hLz'
  rw [att_phi_val, attPhi_apply]
  have hsum : z' 0 + z' 1 + z' 2 = 1 := by
    have h := congrFun (attL_apply z' ▸ hLz') 0
    simpa using h
  have h2 : 0 ≤ z' 2 := hz' 2
  linarith

/-- `(1/2, 1/2, 0)` is not basic, with kernel direction `(1, -1, 0)`. -/
private theorem att_not_basic : ¬ IsBasicPt attL ![1 / 2, 1 / 2, (0 : ℝ)] := by
  intro hbasic
  have hLd : attL ![1, -1, (0 : ℝ)] = 0 := by
    rw [attL_apply]
    funext j
    fin_cases j
    simp
  have hsupp : ∀ i, ![1 / 2, 1 / 2, (0 : ℝ)] i = 0 → ![1, -1, (0 : ℝ)] i = 0 := by
    intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · simp
  have hd0 : ![1, -1, (0 : ℝ)] ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  exact hd0 (hbasic _ hLd hsupp)

/-- The API gives a basic optimum of value 1. -/
private theorem att_basic_opt : ∃ z' : Fin 3 → ℝ,
    0 ≤ z' ∧ attL z' = ![1] ∧ attPhi z' = 1 ∧ IsBasicPt attL z' := by
  obtain ⟨z', hz', hLz', hφz', hbas'⟩ :=
    exists_basic_optimal attL attPhi ![1] att_z_nonneg att_z_eq att_opt
  exact ⟨z', hz', hLz', hφz'.trans att_phi_val, hbas'⟩

private theorem att_finite :
    {z : Fin 3 → ℝ | 0 ≤ z ∧ attL z = ![1] ∧ IsBasicPt attL z}.Finite :=
  finite_basic attL ![1]

/-- `(1, 0, 0)` is feasible, basic and optimal. -/
private theorem att_e0_nonneg : 0 ≤ ![1, 0, (0 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem att_e0_eq : attL ![1, 0, (0 : ℝ)] = ![1] := by
  rw [attL_apply]
  funext j
  fin_cases j
  simp

private theorem att_e0_basic : IsBasicPt attL ![1, 0, (0 : ℝ)] := by
  intro d hLd hsupp
  have h1 : d 1 = 0 := hsupp 1 (by simp)
  have h2 : d 2 = 0 := hsupp 2 (by simp)
  have hsum : d 0 + d 1 + d 2 = 0 := by
    have h := congrFun (attL_apply d ▸ hLd) 0
    simpa using h
  have h0 : d 0 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

private theorem att_e0_opt : attPhi ![1, 0, (0 : ℝ)] = 1 := by
  rw [attPhi_apply]
  simp

/-! ### T-unique (FX02): same `L`, `c`, with `φ = (1, 2, 3)` -/

/-- T-unique objective `φ = (1, 2, 3)`. -/
private noncomputable def uniqPhi : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun z := z 0 + 2 * z 1 + 3 * z 2
  map_add' x y := by
    show (x + y) 0 + 2 * (x + y) 1 + 3 * (x + y) 2
      = (x 0 + 2 * x 1 + 3 * x 2) + (y 0 + 2 * y 1 + 3 * y 2)
    simp [Pi.add_apply]; ring
  map_smul' a x := by
    show (a • x) 0 + 2 * (a • x) 1 + 3 * (a • x) 2 = a • (x 0 + 2 * x 1 + 3 * x 2)
    simp [Pi.smul_apply, smul_eq_mul]; ring

private theorem uniqPhi_apply (z : Fin 3 → ℝ) : uniqPhi z = z 0 + 2 * z 1 + 3 * z 2 := rfl

/-- The optimum is 1, attained only at `(1, 0, 0)`. -/
private theorem uniq_opt : ∀ z' : Fin 3 → ℝ, 0 ≤ z' → attL z' = ![1] →
    1 ≤ uniqPhi z' ∧ (uniqPhi z' = 1 → z' = ![1, 0, (0 : ℝ)]) := by
  intro z' hz' hLz'
  have hsum : z' 0 + z' 1 + z' 2 = 1 := by
    have h := congrFun (attL_apply z' ▸ hLz') 0
    simpa using h
  have h0 : 0 ≤ z' 0 := hz' 0
  have h1 : 0 ≤ z' 1 := hz' 1
  have h2 : 0 ≤ z' 2 := hz' 2
  rw [uniqPhi_apply]
  constructor
  · linarith
  · intro heq
    have e1 : z' 1 = 0 := by linarith
    have e2 : z' 2 = 0 := by linarith
    have e0 : z' 0 = 1 := by linarith
    funext i
    fin_cases i
    · simpa using e0
    · simpa using e1
    · simpa using e2

private theorem uniq_e0_val : uniqPhi ![1, 0, (0 : ℝ)] = 1 := by
  rw [uniqPhi_apply]
  simp

/-- The API gives a basic optimum of value 1, hence `(1, 0, 0)` by uniqueness. -/
private theorem uniq_basic_opt : ∃ z' : Fin 3 → ℝ,
    0 ≤ z' ∧ attL z' = ![1] ∧ uniqPhi z' = 1 ∧ IsBasicPt attL z' := by
  obtain ⟨z', hz', hLz', hφz', hbas'⟩ :=
    exists_basic_optimal attL uniqPhi ![1] att_e0_nonneg att_e0_eq
      (fun z' hz' hLz' => by rw [uniq_e0_val]; exact (uniq_opt z' hz' hLz').1)
  refine ⟨z', hz', hLz', ?_, hbas'⟩
  rw [hφz', uniq_e0_val]

private theorem uniq_api_is_e0 : ∀ z' : Fin 3 → ℝ, 0 ≤ z' → attL z' = ![1] →
    uniqPhi z' = 1 → IsBasicPt attL z' → z' = ![1, 0, (0 : ℝ)] :=
  fun z' hz' hLz' hval _ => (uniq_opt z' hz' hLz').2 hval

/-! ### T-empty (FX03): `L = [[1]]`, `c = (-1)` -/

/-- T-empty constraint map. -/
private noncomputable def emptyL : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
  (Matrix.of ![![1]]).mulVecLin

private theorem emptyL_apply (z : Fin 1 → ℝ) : emptyL z = ![z 0] := by
  funext j
  fin_cases j
  simp [emptyL, Matrix.mulVec, dotProduct]

/-- No feasible point exists, so `exists_basic_optimal` has no hypotheses to meet. -/
private theorem empty_no_feas : ¬ ∃ z : Fin 1 → ℝ, 0 ≤ z ∧ emptyL z = ![-1] := by
  rintro ⟨z, hz, hL⟩
  have h0 : (0 : ℝ) ≤ z 0 := hz 0
  have heq : z 0 = -1 := by
    have h := congrFun (emptyL_apply z ▸ hL) 0
    simpa using h
  linarith

private theorem empty_basic_empty :
    {z : Fin 1 → ℝ | 0 ≤ z ∧ emptyL z = ![-1] ∧ IsBasicPt emptyL z} = ∅ := by
  ext z
  rw [Set.mem_empty_iff_false, iff_false]
  intro hz
  obtain ⟨hz0, hL, -⟩ := hz
  exact absurd ⟨z, hz0, hL⟩ empty_no_feas

private theorem empty_finite :
    {z : Fin 1 → ℝ | 0 ≤ z ∧ emptyL z = ![-1] ∧ IsBasicPt emptyL z}.Finite :=
  finite_basic emptyL ![-1]

/-! ### T-iota-empty (FX04): `ι = Fin 0` -/

/-- T-iota-empty constraint map (the only map out of the empty product). -/
private noncomputable def iotaL : (Fin 0 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := 0

/-- The empty vector is the only feasible point for `c = 0`. -/
private theorem iota_only : ∀ z : Fin 0 → ℝ, 0 ≤ z → iotaL z = 0 → z = 0 := by
  intro z _ _
  funext i
  nomatch i

/-- The empty vector is basic vacuously. -/
private theorem iota_basic : IsBasicPt iotaL 0 := by
  intro d _ _
  funext i
  nomatch i

private theorem iota_api : ∃ z' : Fin 0 → ℝ,
    0 ≤ z' ∧ iotaL z' = 0 ∧ (0 : (Fin 0 → ℝ) →ₗ[ℝ] ℝ) z' = 0 ∧ IsBasicPt iotaL z' := by
  obtain ⟨z', hz', hLz', hφz', hbas'⟩ :=
    exists_basic_optimal iotaL 0 0 le_rfl (map_zero _) (fun z' _ _ => by simp)
  exact ⟨z', hz', hLz', hφz'.trans (by simp), hbas'⟩

/-- With `c ≠ 0` nothing is feasible. -/
private theorem iota_none : ¬ ∃ z : Fin 0 → ℝ, 0 ≤ z ∧ iotaL z = ![1] := by
  rintro ⟨z, -, hL⟩
  have hz : iotaL z = 0 := by simp [iotaL]
  rw [hz] at hL
  have := congrFun hL 0
  simp at this

/-! ### T-degenerate (FX05): `L = [[1, 1, 0], [1, 0, 1]]`, `c = (1, 1)` -/

/-- T-degenerate constraint map. -/
private noncomputable def degL : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (Matrix.of ![![1, 1, 0], ![1, 0, 1]]).mulVecLin

private theorem degL_apply (z : Fin 3 → ℝ) : degL z = ![z 0 + z 1, z 0 + z 2] := by
  funext j
  fin_cases j <;> simp [degL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `(1, 0, 0)` is feasible and basic, with a single positive entry. -/
private theorem deg_p1_nonneg : 0 ≤ ![1, 0, (0 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem deg_p1_eq : degL ![1, 0, (0 : ℝ)] = ![1, 1] := by
  rw [degL_apply]
  funext j
  fin_cases j <;> simp

private theorem deg_p1_basic : IsBasicPt degL ![1, 0, (0 : ℝ)] := by
  intro d hLd hsupp
  have h1 : d 1 = 0 := hsupp 1 (by simp)
  have h2 : d 2 = 0 := hsupp 2 (by simp)
  have hr0 : d 0 + d 1 = 0 := by
    have h := congrFun (degL_apply d ▸ hLd) 0
    simpa using h
  have hr1 : d 0 + d 2 = 0 := by
    have h := congrFun (degL_apply d ▸ hLd) 1
    simpa using h
  have h0 : d 0 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

private theorem deg_p1_support : ∀ i : Fin 3, ![1, 0, (0 : ℝ)] i ≠ 0 → i = 0 := by
  intro i hi
  fin_cases i
  · rfl
  · simp at hi
  · simp at hi

/-- `degL` is surjective: a target `(a, b)` is the image of `(0, a, b)`. -/
private theorem degL_surjective : Function.Surjective degL := by
  intro y
  refine ⟨![0, y 0, y 1], ?_⟩
  rw [degL_apply]
  funext j
  fin_cases j <;> simp

/-- `degL` has rank 2. -/
private theorem deg_rank_two : Module.finrank ℝ (LinearMap.range degL) = 2 := by
  have hrange : LinearMap.range degL = ⊤ := LinearMap.range_eq_top.mpr degL_surjective
  rw [hrange, Submodule.topEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-- `(0, 1, 1)` is feasible and basic. -/
private theorem deg_p2_nonneg : 0 ≤ ![0, 1, (1 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem deg_p2_eq : degL ![0, 1, (1 : ℝ)] = ![1, 1] := by
  rw [degL_apply]
  funext j
  fin_cases j <;> simp

private theorem deg_p2_basic : IsBasicPt degL ![0, 1, (1 : ℝ)] := by
  intro d hLd hsupp
  have h0 : d 0 = 0 := hsupp 0 (by simp)
  have hr0 : d 0 + d 1 = 0 := by
    have h := congrFun (degL_apply d ▸ hLd) 0
    simpa using h
  have hr1 : d 0 + d 2 = 0 := by
    have h := congrFun (degL_apply d ▸ hLd) 1
    simpa using h
  have h1 : d 1 = 0 := by linarith
  have h2 : d 2 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

private theorem deg_finite :
    {z : Fin 3 → ℝ | 0 ≤ z ∧ degL z = ![1, 1] ∧ IsBasicPt degL z}.Finite :=
  finite_basic degL ![1, 1]

/-- The midpoint `(1/2, 1/2, 1/2)` is feasible and not basic. -/
private theorem deg_mid_nonneg : 0 ≤ ![1 / 2, 1 / 2, (1 / 2 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem deg_mid_eq : degL ![1 / 2, 1 / 2, (1 / 2 : ℝ)] = ![1, 1] := by
  rw [degL_apply]
  funext j
  fin_cases j <;> simp <;> norm_num

private theorem deg_mid_not_basic : ¬ IsBasicPt degL ![1 / 2, 1 / 2, (1 / 2 : ℝ)] := by
  intro hbasic
  have hLd : degL ![1, -1, (-1 : ℝ)] = 0 := by
    rw [degL_apply]
    funext j
    fin_cases j <;> simp
  have hsupp : ∀ i, ![1 / 2, 1 / 2, (1 / 2 : ℝ)] i = 0 → ![1, -1, (-1 : ℝ)] i = 0 := by
    intro i hi
    fin_cases i <;> simp at hi
  have hd0 : ![1, -1, (-1 : ℝ)] ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  exact hd0 (hbasic _ hLd hsupp)

/-- The basic feasible points are exactly `(1, 0, 0)` and `(0, 1, 1)`. -/
private theorem deg_basic_exact : ∀ z : Fin 3 → ℝ,
    (0 ≤ z ∧ degL z = ![1, 1] ∧ IsBasicPt degL z) ↔
      (z = ![1, 0, (0 : ℝ)] ∨ z = ![0, 1, (1 : ℝ)]) := by
  intro z
  classical
  constructor
  · rintro ⟨hz, hL, hbasic⟩
    have hr0 : z 0 + z 1 = 1 := by
      have h := congrFun (degL_apply z ▸ hL) 0
      simpa using h
    have hr1 : z 0 + z 2 = 1 := by
      have h := congrFun (degL_apply z ▸ hL) 1
      simpa using h
    have h0 : 0 ≤ z 0 := hz 0
    have h1 : 0 ≤ z 1 := hz 1
    have h2 : 0 ≤ z 2 := hz 2
    by_cases hz0 : z 0 = 0
    · right
      have e1 : z 1 = 1 := by linarith
      have e2 : z 2 = 1 := by linarith
      funext i
      fin_cases i
      · simpa using hz0
      · simpa using e1
      · simpa using e2
    · by_cases hz1 : z 1 = 0
      · left
        have e0 : z 0 = 1 := by linarith
        have e2 : z 2 = 0 := by linarith
        funext i
        fin_cases i
        · simpa using e0
        · simpa using hz1
        · simpa using e2
      · by_cases hz2 : z 2 = 0
        · left
          have e0 : z 0 = 1 := by linarith
          have e1 : z 1 = 0 := by linarith
          funext i
          fin_cases i
          · simpa using e0
          · simpa using e1
          · simpa using hz2
        · exfalso
          have hLd : degL ![1, -1, (-1 : ℝ)] = 0 := by
            rw [degL_apply]
            funext j
            fin_cases j <;> simp
          have hsupp : ∀ i, z i = 0 → ![1, -1, (-1 : ℝ)] i = 0 := by
            intro i hi
            fin_cases i
            · exact absurd hi hz0
            · exact absurd hi hz1
            · exact absurd hi hz2
          have hd0 : ![1, -1, (-1 : ℝ)] ≠ (0 : Fin 3 → ℝ) := by
            intro h
            have := congrFun h 0
            simp at this
          exact hd0 (hbasic _ hLd hsupp)
  · rintro (rfl | rfl)
    · exact ⟨deg_p1_nonneg, deg_p1_eq, deg_p1_basic⟩
    · exact ⟨deg_p2_nonneg, deg_p2_eq, deg_p2_basic⟩

/-! ### T-redundant (FX06): `L = [[1, 1], [2, 2]]`, `c = (1, 2)` -/

/-- T-redundant constraint map. -/
private noncomputable def redL : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (Matrix.of ![![1, 1], ![2, 2]]).mulVecLin

private theorem redL_apply (z : Fin 2 → ℝ) : redL z = ![z 0 + z 1, 2 * z 0 + 2 * z 1] := by
  funext j
  fin_cases j <;> simp [redL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `(1, 0)` is feasible and basic. -/
private theorem red_e0_nonneg : 0 ≤ ![1, (0 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem red_e0_eq : redL ![1, (0 : ℝ)] = ![1, 2] := by
  rw [redL_apply]
  funext j
  fin_cases j <;> simp

private theorem red_e0_basic : IsBasicPt redL ![1, (0 : ℝ)] := by
  intro d hLd hsupp
  have h1 : d 1 = 0 := hsupp 1 (by simp)
  have hr0 : d 0 + d 1 = 0 := by
    have h := congrFun (redL_apply d ▸ hLd) 0
    simpa using h
  have h0 : d 0 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- `(0, 1)` is feasible and basic. -/
private theorem red_e1_nonneg : 0 ≤ ![0, (1 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem red_e1_eq : redL ![0, (1 : ℝ)] = ![1, 2] := by
  rw [redL_apply]
  funext j
  fin_cases j <;> simp

private theorem red_e1_basic : IsBasicPt redL ![0, (1 : ℝ)] := by
  intro d hLd hsupp
  have h0 : d 0 = 0 := hsupp 0 (by simp)
  have hr0 : d 0 + d 1 = 0 := by
    have h := congrFun (redL_apply d ▸ hLd) 0
    simpa using h
  have h1 : d 1 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

private theorem red_finite :
    {z : Fin 2 → ℝ | 0 ≤ z ∧ redL z = ![1, 2] ∧ IsBasicPt redL z}.Finite :=
  finite_basic redL ![1, 2]

/-- The basic feasible points are exactly `(1, 0)` and `(0, 1)`. -/
private theorem red_basic_exact : ∀ z : Fin 2 → ℝ,
    (0 ≤ z ∧ redL z = ![1, 2] ∧ IsBasicPt redL z) ↔
      (z = ![1, (0 : ℝ)] ∨ z = ![0, (1 : ℝ)]) := by
  intro z
  classical
  constructor
  · rintro ⟨hz, hL, hbasic⟩
    have hsum : z 0 + z 1 = 1 := by
      have h := congrFun (redL_apply z ▸ hL) 0
      simpa using h
    have h0 : 0 ≤ z 0 := hz 0
    have h1 : 0 ≤ z 1 := hz 1
    by_cases hz0 : z 0 = 0
    · right
      have e1 : z 1 = 1 := by linarith
      funext i
      fin_cases i
      · simpa using hz0
      · simpa using e1
    · by_cases hz1 : z 1 = 0
      · left
        have e0 : z 0 = 1 := by linarith
        funext i
        fin_cases i
        · simpa using e0
        · simpa using hz1
      · exfalso
        have hLd : redL ![1, (-1 : ℝ)] = 0 := by
          rw [redL_apply]
          funext j
          fin_cases j <;> simp
        have hsupp : ∀ i, z i = 0 → ![1, (-1 : ℝ)] i = 0 := by
          intro i hi
          fin_cases i
          · exact absurd hi hz0
          · exact absurd hi hz1
        have hd0 : ![1, (-1 : ℝ)] ≠ (0 : Fin 2 → ℝ) := by
          intro h
          have := congrFun h 0
          simp at this
        exact hd0 (hbasic _ hLd hsupp)
  · rintro (rfl | rfl)
    · exact ⟨red_e0_nonneg, red_e0_eq, red_e0_basic⟩
    · exact ⟨red_e1_nonneg, red_e1_eq, red_e1_basic⟩

/-! ### T-unbounded (FX07, FX08): `L = [[1, -1]]`, `c = (1)` -/

/-- T-unbounded constraint map. -/
private noncomputable def unbL : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
  (Matrix.of ![![1, -1]]).mulVecLin

private theorem unbL_apply (z : Fin 2 → ℝ) : unbL z = ![z 0 - z 1] := by
  funext j
  fin_cases j
  simp [unbL, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-- T-unbounded objective `φ = (0, 1)`, minimized at `(1, 0)` with value 0. -/
private noncomputable def unbPhi : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

private theorem unbPhi_apply (z : Fin 2 → ℝ) : unbPhi z = z 1 := by
  simp [unbPhi]

private theorem unb_e0_nonneg : 0 ≤ ![1, (0 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem unb_e0_eq : unbL ![1, (0 : ℝ)] = ![1] := by
  rw [unbL_apply]
  funext j
  fin_cases j
  simp

private theorem unb_opt : ∀ z' : Fin 2 → ℝ, 0 ≤ z' → unbL z' = ![1] →
    unbPhi ![1, (0 : ℝ)] ≤ unbPhi z' := by
  intro z' hz' _
  rw [unbPhi_apply, unbPhi_apply]
  simpa using hz' 1

private theorem unb_e0_basic : IsBasicPt unbL ![1, (0 : ℝ)] := by
  intro d hLd hsupp
  have h1 : d 1 = 0 := hsupp 1 (by simp)
  have hr : d 0 - d 1 = 0 := by
    have h := congrFun (unbL_apply d ▸ hLd) 0
    simpa using h
  have h0 : d 0 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

private theorem unb_basic_opt : ∃ z' : Fin 2 → ℝ,
    0 ≤ z' ∧ unbL z' = ![1] ∧ unbPhi z' = 0 ∧ IsBasicPt unbL z' := by
  obtain ⟨z', hz', hLz', hφz', hbas'⟩ :=
    exists_basic_optimal unbL unbPhi ![1] unb_e0_nonneg unb_e0_eq unb_opt
  have hval : unbPhi ![1, (0 : ℝ)] = 0 := by rw [unbPhi_apply]; simp
  exact ⟨z', hz', hLz', hφz'.trans hval, hbas'⟩

/-- `φ = (-1, 0)` is unbounded below. -/
private noncomputable def unbPhi2 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun z := -z 0
  map_add' x y := by
    show -((x + y) 0) = -x 0 + -y 0
    simp [Pi.add_apply]; ring
  map_smul' a x := by
    show -((a • x) 0) = a • (-x 0)
    simp [Pi.smul_apply, smul_eq_mul]

private theorem unbPhi2_apply (z : Fin 2 → ℝ) : unbPhi2 z = -z 0 := rfl

/-- Attainment cannot be dropped: `hopt` fails at `(1, 0)` since `(2, 1)` is better. -/
private theorem unb_no_opt : ¬ ∀ z' : Fin 2 → ℝ, 0 ≤ z' → unbL z' = ![1] →
    unbPhi2 ![1, (0 : ℝ)] ≤ unbPhi2 z' := by
  intro hopt
  have hfeas : (0 : Fin 2 → ℝ) ≤ ![2, (1 : ℝ)] := by
    intro i
    fin_cases i <;> simp
  have hL : unbL ![2, (1 : ℝ)] = ![1] := by
    rw [unbL_apply]
    funext j
    fin_cases j
    simp
    norm_num
  have hle := hopt _ hfeas hL
  rw [unbPhi2_apply, unbPhi2_apply] at hle
  simp at hle

/-- With `c = 0`, the only basic feasible point is `0`. -/
private theorem unb_c0_basic_eq_zero : ∀ z : Fin 2 → ℝ, 0 ≤ z → unbL z = 0 →
    IsBasicPt unbL z → z = 0 := by
  intro z hz hL hbasic
  by_contra hne
  have hsub : z 0 - z 1 = 0 := by
    have h := congrFun (unbL_apply z ▸ hL) 0
    simpa using h
  have h01 : z 0 = z 1 := by linarith
  have hne0 : (0 : ℝ) ≠ z 0 := by
    intro h00
    apply hne
    have hz0 : z 0 = 0 := h00.symm
    have hz1 : z 1 = 0 := by linarith
    funext i
    fin_cases i
    · simpa using hz0
    · simpa using hz1
  have hpos : 0 < z 0 := lt_of_le_of_ne (hz 0) hne0
  have hLd1 : unbL ![1, (1 : ℝ)] = 0 := by
    rw [unbL_apply]
    funext j
    fin_cases j
    simp
  have hsupp : ∀ i, z i = 0 → ![1, (1 : ℝ)] i = 0 := by
    intro i hi
    fin_cases i
    · simp at hi
      exfalso
      linarith
    · simp at hi
      exfalso
      linarith
  have hd0 : ![1, (1 : ℝ)] ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  exact hd0 (hbasic _ hLd1 hsupp)

private theorem unb_c0_zero_basic :
    (0 : Fin 2 → ℝ) ≤ 0 ∧ unbL 0 = 0 ∧ IsBasicPt unbL 0 := by
  refine ⟨le_rfl, map_zero _, fun d _ hsupp => ?_⟩
  funext i
  fin_cases i
  · simpa using hsupp 0 (by simp)
  · simpa using hsupp 1 (by simp)

/-! ### T-constant (FX09): the zero functional gives a basic feasible point -/

private theorem const_basic_pt : ∃ z' : Fin 3 → ℝ,
    0 ≤ z' ∧ attL z' = ![1] ∧ IsBasicPt attL z' := by
  obtain ⟨z', hz', hLz', -, hbas'⟩ :=
    exists_basic_optimal attL 0 ![1] att_e0_nonneg att_e0_eq (fun z' _ _ => by simp)
  exact ⟨z', hz', hLz', hbas'⟩

/-! ### T-general-E: `E = ℝ` -/

/-- T-general-E constraint map: a single linear functional. -/
private noncomputable def genL : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun z := z 0 + z 1
  map_add' x y := by
    show (x + y) 0 + (x + y) 1 = (x 0 + x 1) + (y 0 + y 1)
    simp [Pi.add_apply]; ring
  map_smul' a x := by
    show (a • x) 0 + (a • x) 1 = a • (x 0 + x 1)
    simp [Pi.smul_apply, smul_eq_mul]; ring

private theorem genL_apply (z : Fin 2 → ℝ) : genL z = z 0 + z 1 := rfl

/-- T-general-E objective: minimize the first coordinate. -/
private noncomputable def genPhi : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0

private theorem genPhi_apply (z : Fin 2 → ℝ) : genPhi z = z 0 := by
  simp [genPhi]

private theorem gen_e1_nonneg : 0 ≤ ![0, (1 : ℝ)] := by
  intro i
  fin_cases i <;> simp

private theorem gen_e1_eq : genL ![0, (1 : ℝ)] = 1 := by
  rw [genL_apply]
  simp

private theorem gen_opt : ∀ z' : Fin 2 → ℝ, 0 ≤ z' → genL z' = 1 →
    genPhi ![0, (1 : ℝ)] ≤ genPhi z' := by
  intro z' hz' _
  rw [genPhi_apply, genPhi_apply]
  simpa using hz' 0

private theorem gen_e1_basic : IsBasicPt genL ![0, (1 : ℝ)] := by
  intro d hLd hsupp
  have h0 : d 0 = 0 := hsupp 0 (by simp)
  have hsum : d 0 + d 1 = 0 := genL_apply d ▸ hLd
  have h1 : d 1 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1

private theorem gen_basic_opt : ∃ z' : Fin 2 → ℝ,
    0 ≤ z' ∧ genL z' = 1 ∧ genPhi z' = 0 ∧ IsBasicPt genL z' := by
  obtain ⟨z', hz', hLz', hφz', hbas'⟩ :=
    exists_basic_optimal genL genPhi 1 gen_e1_nonneg gen_e1_eq gen_opt
  have hval : genPhi ![0, (1 : ℝ)] = 0 := by rw [genPhi_apply]; simp
  exact ⟨z', hz', hLz', hφz'.trans hval, hbas'⟩

private theorem gen_finite :
    {z : Fin 2 → ℝ | 0 ≤ z ∧ genL z = 1 ∧ IsBasicPt genL z}.Finite :=
  finite_basic genL 1

#print axioms att_basic_opt
#print axioms uniq_basic_opt
#print axioms empty_finite
#print axioms iota_api
#print axioms deg_p1_basic
#print axioms unb_basic_opt
#print axioms const_basic_pt
#print axioms gen_basic_opt

/-! ### OPT-005b: basic points are extreme points -/

private theorem att_e0_mem_extremePoints :
    ![1, 0, (0 : ℝ)] ∈ Set.extremePoints ℝ {w | 0 ≤ w ∧ attL w = ![1]} :=
  (isBasicPt_iff_mem_extremePoints attL ![1] att_e0_nonneg att_e0_eq).mp att_e0_basic

private theorem att_mid_not_mem_extremePoints :
    ![1 / 2, 1 / 2, (0 : ℝ)] ∉ Set.extremePoints ℝ {w | 0 ≤ w ∧ attL w = ![1]} := by
  intro hmem
  exact att_not_basic
    ((isBasicPt_iff_mem_extremePoints attL ![1] att_z_nonneg att_z_eq).mpr hmem)

private theorem iota_zero_mem_extremePoints :
    (0 : Fin 0 → ℝ) ∈ Set.extremePoints ℝ {w | 0 ≤ w ∧ iotaL w = 0} :=
  (isBasicPt_iff_mem_extremePoints iotaL 0 le_rfl (map_zero _)).mp iota_basic

end MathlibExtTest.Analysis.Convex.LinearProgrammingBasic
