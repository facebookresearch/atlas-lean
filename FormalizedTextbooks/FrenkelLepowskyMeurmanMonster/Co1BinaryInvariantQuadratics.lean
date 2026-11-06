/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryInvariantForms
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The genuine Conway module has a unique nonzero invariant quadratic form. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- There is no nonzero linear functional invariant under the actual full Conway action. -/
theorem co1BinaryAction_invariant_functional_zero
    (f : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ g : Co1, ∀ x, f (co1BinaryAction g x) = f x) : f = 0 := by
  have hk : ∀ g : Co1, ∀ x, x ∈ LinearMap.ker f →
      co1BinaryAction g x ∈ LinearMap.ker f := by
    intro g x hx
    change f (co1BinaryAction g x) = 0
    rw [hf, show f x = 0 from hx]
  rcases co1BinaryAction_invariant_subspace_dichotomy (LinearMap.ker f) hk with hb | ht
  · have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hb)
    norm_num [Module.finrank_pi, Module.finrank_self] at hd
  · apply LinearMap.ext
    intro x
    have hx : x ∈ LinearMap.ker f := by rw [ht]; trivial
    exact hx

/-- An invariant quadratic form with zero polar pairing is zero. -/
theorem co1BinaryAction_invariant_quadratic_zero_of_polar_zero
    (Q : QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2))
    (hQ : ∀ g : Co1, ∀ x, Q (co1BinaryAction g x) = Q x)
    (hp : Q.polarBilin = 0) : Q = 0 := by
  let f : (Fin 24 → ZMod 2) →+ ZMod 2 :=
    { toFun := Q
      map_zero' := Q.map_zero
      map_add' := fun x y => by
        have h : QuadraticMap.polar Q x y = 0 := by
          exact congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2) => B x y) hp
        rw [QuadraticMap.map_add (Q : (Fin 24 → ZMod 2) → ZMod 2) x y, h, add_zero] }
  let F : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { f with map_smul' := ZMod.map_smul f }
  have hf := co1BinaryAction_invariant_functional_zero F hQ
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun hf x

/-- Invariance under actual Conway elements and the polar form determine the quadratic form. -/
theorem co1BinaryAction_invariant_quadratic_eq_of_polar_eq
    (P Q : QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2))
    (hP : ∀ g : Co1, ∀ x, P (co1BinaryAction g x) = P x)
    (hQ : ∀ g : Co1, ∀ x, Q (co1BinaryAction g x) = Q x)
    (hp : P.polarBilin = Q.polarBilin) : P = Q := by
  have hzero : (P - Q).polarBilin = 0 := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    have h := congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2) => B x y) hp
    change P (x + y) - P x - P y = Q (x + y) - Q x - Q y at h
    change (P (x + y) - Q (x + y)) - (P x - Q x) - (P y - Q y) = 0
    linear_combination h
  have hi : ∀ g : Co1, ∀ x, (P - Q) (co1BinaryAction g x) = (P - Q) x := by
    intro g x
    change P (co1BinaryAction g x) - Q (co1BinaryAction g x) = P x - Q x
    rw [hP, hQ]
  exact sub_eq_zero.mp
    (co1BinaryAction_invariant_quadratic_zero_of_polar_zero (P - Q) hi hzero)

/-- The original squares form is invariant under the actual Conway group. -/
theorem co1BinaryAction_squareQuad_invariant (g : Co1) (x : Fin 24 → ZMod 2) :
    squareQuad (co1BinaryAction g x) = squareQuad x := by
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective signsSubgroup g
  exact leechBinaryAction_squareQuad e x

/-- The only quadratic forms invariant under the actual Conway action are zero and squares. -/
theorem co1BinaryAction_invariant_quadratic_zero_or_squareQuad
    (Q : QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2))
    (hQ : ∀ g : Co1, ∀ x, Q (co1BinaryAction g x) = Q x) :
    Q = 0 ∨ Q = squareQuad := by
  have hi : ∀ g : Co1, ∀ x y,
      Q.polarBilin (co1BinaryAction g x) (co1BinaryAction g y) = Q.polarBilin x y := by
    intro g x y
    change Q (co1BinaryAction g x + co1BinaryAction g y) -
      Q (co1BinaryAction g x) - Q (co1BinaryAction g y) = Q (x + y) - Q x - Q y
    rw [← map_add, hQ, hQ, hQ]
  rcases co1BinaryAction_invariant_bilinear_zero_or_polar Q.polarBilin hi with hz | hp
  · exact Or.inl (co1BinaryAction_invariant_quadratic_zero_of_polar_zero Q hQ hz)
  · right
    apply co1BinaryAction_invariant_quadratic_eq_of_polar_eq Q squareQuad hQ
      co1BinaryAction_squareQuad_invariant
    exact hp.trans (LinearMap.BilinMap.polarBilin_toQuadraticMap (B := qBilin)).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
