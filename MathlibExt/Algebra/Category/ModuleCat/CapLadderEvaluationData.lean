/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Cap-ladder evaluation as a product of incidence scalars

Let R be a commutative ring in universe u. A ladder consists of module families U_j,V_j, maps
u_j:U_j→U_{j+1} and v_j:V_{j+1}→V_j, pairings E_j:U_j⊗_R V_j→R, chosen elements p_j∈U_j and
b_j∈V_j, and scalars s_j∈R.

The laws are p_{j+1}=u_j(p_j), E_{j+1}(u_j(a)⊗b)=E_j(a⊗v_j(b)), v_j(b_{j+1})=s_j•b_j, and
E₀(p₀⊗b₀)=1. They imply E_j(p_j⊗b_j)=∏_{i<j}s_i for every natural rung j. If every scalar below
j is a unit, this evaluation is a unit as well.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat

/-- Let R be a commutative ring in universe u. A cap ladder has modules U_j,V_j, ascent maps
u_j:U_j→U_{j+1}, descent maps v_j:V_{j+1}→V_j, and pairings E_j:U_j⊗_R V_j→R. The data also
choose p_j∈U_j, b_j∈V_j, and s_j∈R, with p_{j+1}=u_j(p_j), E_{j+1}(u_j(a)⊗b)=E_j(a⊗v_j(b)),
v_j(b_{j+1})=s_j•b_j, and E₀(p₀⊗b₀)=1. All module carriers lie in u, and s_j belongs to the
transition from j+1 down to j. -/
@[ext]
structure CapLadderEvaluationData (R : Type u) [CommRing R] where
  /-- Let R be a commutative ring in universe u. The field U:ℕ→ModuleCat_u(R) gives the module on each
  ascending rung j. The ladder's ascent step u_j maps U_j to U_{j+1}, and its chosen power p_j
  lies in U_j. -/
  cohomology : ℕ → ModuleCat.{u} R
  /-- Let R be a commutative ring in universe u. The field V:ℕ→ModuleCat_u(R) gives the module on each
  descending rung j. Its descent map v_j has source V_{j+1} and target V_j, and the chosen
  homology element b_j belongs to V_j. -/
  homology : ℕ → ModuleCat.{u} R
  /-- Let R be a commutative ring in universe u. For a ladder's family U_j, the field u_j:U_j→U_{j+1}
  is an R-linear map for every j≥0. The power recurrence requires p_{j+1}=u_j(p_j), and the
  evaluation compatibility pairs this step with the descent v_j. -/
  cupStep : ∀ j, cohomology j ⟶ cohomology (j + 1)
  /-- Let R be a commutative ring in universe u. For a ladder's family V_j, the field v_j:V_{j+1}→V_j
  is an R-linear map. The chosen elements satisfy v_j(b_{j+1})=s_j•b_j, so the scalar s_j is
  attached to this downward transition. -/
  capStep : ∀ j, homology (j + 1) ⟶ homology j
  /-- Let R be a commutative ring in universe u. For each j≥0, the evaluation is an R-linear map
  E_j:U_j⊗_R V_j→R. On a pure tensor a⊗b it pairs the ascending element a with the descending
  element b, and its step compatibility is E_{j+1}(u_j(a)⊗b)=E_j(a⊗v_j(b)). -/
  pairing : ∀ j,
    MonoidalCategory.tensorObj (cohomology j) (homology j) ⟶ ModuleCat.of R R
  /-- Let R be a commutative ring in universe u. The field p_j∈U_j specifies the chosen ascending
  element for every j≥0. These choices are related by the separate recurrence p_{j+1}=u_j(p_j),
  and are the inputs evaluated by E_j against b_j. -/
  power : ∀ j, cohomology j
  /-- Let R be a commutative ring in universe u. For each j≥0, the field b_j∈V_j specifies the chosen
  descending coefficient. The incidence law sends b_{j+1} under v_j to s_j•b_j, and E_j evaluates
  it against the chosen ascending p_j. -/
  homologyElement : ∀ j, homology j
  /-- Let R be a commutative ring in universe u. The field s:ℕ→R gives one coefficient scalar s_j for
  each downward transition v_j:V_{j+1}→V_j. It appears in v_j(b_{j+1})=s_j•b_j and in the
  evaluation product ∏_{i<j}s_i. -/
  scalar : ℕ → R
  /-- Let R be a commutative ring in universe u. For every j≥0, the ladder law is p_{j+1}=u_j(p_j) in
  U_{j+1}, where u_j:U_j→U_{j+1} is its ascent step. This is the compatibility of the chosen
  powers with the step maps. -/
  power_succ : ∀ j, power (j + 1) = (cupStep j).hom (power j)
  /-- Let R be a commutative ring in universe u. A cap ladder has modules U_j,V_j, ascent maps
  u_j:U_j→U_{j+1}, descent maps v_j:V_{j+1}→V_j, and pairings E_j:U_j⊗_R V_j→R. For every j≥0,
  a∈U_j, and b∈V_{j+1}, the compatibility law is E_{j+1}(u_j(a)⊗b)=E_j(a⊗v_j(b)). Both evaluations
  lie in R. -/
  pairing_step : ∀ j (a : cohomology j) (b : homology (j + 1)),
    (pairing (j + 1)).hom ((cupStep j).hom a ⊗ₜ[R] b) =
      (pairing j).hom (a ⊗ₜ[R] (capStep j).hom b)
  /-- Let R be a commutative ring in universe u. For every j≥0, the chosen elements b_j∈V_j satisfy
  v_j(b_{j+1})=s_j•b_j. The equality is in V_j and uses the scalar of the transition from j+1 to
  j. -/
  cap_homologyElement : ∀ j,
    (capStep j).hom (homologyElement (j + 1)) = scalar j • homologyElement j
  /-- Let R be a commutative ring in universe u. The ladder's initial normalization is E₀(p₀⊗b₀)=1 in
  R, with p₀∈U₀ and b₀∈V₀. This supplies the empty-product value for the evaluation recurrence. -/
  pairing_zero : (pairing 0).hom (power 0 ⊗ₜ[R] homologyElement 0) = 1

namespace CapLadderEvaluationData

variable {R : Type u} [CommRing R]

/-- Let R be a commutative ring in universe u. For a cap ladder L and every natural j,
E_j(p_j⊗b_j)=∏_{i=0}^{j-1}s_i. The power recurrence, pairing-step compatibility, scalar descent
law, and bottom evaluation one are the ladder hypotheses. At j=0 the product is empty and equals
one. -/
theorem pairing_power_homologyElement (L : CapLadderEvaluationData R) (j : ℕ) :
    (L.pairing j).hom (L.power j ⊗ₜ[R] L.homologyElement j) =
      ∏ i ∈ Finset.range j, L.scalar i := by
  induction j with
  | zero => simpa using L.pairing_zero
  | succ j ih =>
      rw [L.power_succ j, L.pairing_step j, L.cap_homologyElement j,
        TensorProduct.tmul_smul, map_smul, ih, smul_eq_mul,
        Finset.prod_range_succ, mul_comm]

/-- Let R be a commutative ring in universe u. For a cap ladder L and j≥0, if every s_i with i<j is
a unit of R, then E_j(p_j⊗b_j) is a unit. The evaluation equals the finite product ∏_{i<j}s_i,
including the empty product at the bottom rung. -/
theorem isUnit_pairing_power_homologyElement
    (L : CapLadderEvaluationData R) (j : ℕ)
    (hscalar : ∀ i < j, IsUnit (L.scalar i)) :
    IsUnit ((L.pairing j).hom (L.power j ⊗ₜ[R] L.homologyElement j)) := by
  rw [L.pairing_power_homologyElement]
  exact IsUnit.prod_iff.mpr fun i hi ↦ hscalar i (Finset.mem_range.mp hi)

end CapLadderEvaluationData

end ModuleCat

end
