/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generation of a natural coproduct with a zero tail

Let R be a ring in universe u and M_r left R-modules with carriers in an independent universe v,
indexed by natural r. If every M_r with r≤N is finitely generated and every M_r with r>N is
zero, then ⊕_{r∈ℕ}M_r is finitely generated.

The inclusion from the finite initial coproduct ⊕_{r=0}^N M_r has a right inverse defined by
retaining the initial legs and sending the zero tail to zero. Thus the natural coproduct is a
quotient of a finitely generated module.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe u v
variable {R : Type u} [Ring R]

/-- Let R be a ring in universe u, M:ℕ→ModuleCat_v(R), and N a natural number, with coefficient
universe v independent of u. Assume M_r is finitely generated over R for every r≤N and is a zero
object for every r>N. Then the coproduct ⊕_{r∈ℕ}M_r is finitely generated as a left R-module;
the finite initial coproduct covers it through its canonical legs. -/
theorem coproduct_finite_of_zero_above
    (M : ℕ → ModuleCat.{v} R) (N : ℕ)
    (hM : ∀ r : ℕ, r ≤ N → Module.Finite R (M r))
    (hZero : ∀ r : ℕ, N < r → IsZero (M r)) :
    Module.Finite R ↥(∐ M : ModuleCat.{v} R) := by
  classical
  let F : Fin (N + 1) → ModuleCat.{v} R := fun a => M a.val
  let cover : (∐ F) ⟶ ∐ M := Sigma.desc (fun a => Sigma.ι M a.val)
  let liftLeg : ∀ r : ℕ, M r ⟶ ∐ F := fun r =>
    if hr : r ≤ N then Sigma.ι F ⟨r, by omega⟩ else 0
  let retract : (∐ M) ⟶ ∐ F := Sigma.desc liftLeg
  have hRightInverse : retract ≫ cover = 𝟙 (∐ M) := by
    apply Sigma.hom_ext
    intro r
    rw [← Category.assoc]
    dsimp only [retract]
    rw [Sigma.ι_comp_desc]
    by_cases hr : r ≤ N
    · dsimp only [liftLeg]
      rw [dite_eq_left hr]
      dsimp only [cover]
      rw [Sigma.ι_comp_desc, Category.comp_id]
    · exact (hZero r (by omega)).eq_of_src _ _
  let : ∀ a : Fin (N + 1), Module.Finite R (F a) := fun a => hM a.val (by omega)
  let : Module.Finite R (DirectSum (Fin (N + 1)) (fun a => (F a : Type v))) :=
    Module.Finite.equiv
      (DirectSum.linearEquivFunOnFintype R (Fin (N + 1)) (fun a => F a)).symm
  let : Module.Finite R ↥(∐ F : ModuleCat.{v} R) :=
    (Module.Finite.equiv_iff (ModuleCat.coprodIsoDirectSum F).toLinearEquiv).mpr inferInstance
  apply Module.Finite.of_surjective cover.hom
  intro x
  refine ⟨retract.hom x, ?_⟩
  have h := congrArg (fun f : (∐ M) ⟶ ∐ M => f.hom x) hRightInverse
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using h

end ModuleCat
