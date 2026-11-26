/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionAdjunction
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The continuous coinduction monad

Let G be a compact, totally disconnected topological group in universe u and let the discrete
continuous abelian coefficients lie in W=max(u,w). The forgetful functor U has right adjoint C₀,
where C₀(M) is the continuous function group C(G,M) with left-translation action. Untwisting
identifies C₀U with diagonal coinduction C, whose action is (h•F)(g)=h•F(h⁻¹g).

Transporting the adjunction monad along this natural isomorphism gives a monad with underlying
functor C. Its unit sends a coefficient to the constant function g↦a. Its multiplication
evaluates the two nested function coordinates diagonally, F↦(g↦F(g)(g)).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DiscreteAbelianAction
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Let U forget the G-action, C₀ be its
continuous coinduction right adjoint, and u:C₀U≅C be the untwist to diagonal coinduction.
Transporting the monad of U⊣C₀ along u gives a monad on discrete continuous abelian actions with
underlying functor C, unit a↦(g↦a), and multiplication F↦(g↦F(g)(g)). -/
def coindMonad : Monad (DiscreteAbelianAction.{u, max u w} G) :=
  (forgetCoindAdjunction.{u, w} G).toMonad.transport (coindUntwistNatIso.{u, w} G)

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). The monad obtained from the
forgetful/coinduction adjunction by untwisting has underlying endofunctor equal to diagonal
continuous coinduction C. Its objects are C(G,A) with action (h•F)(g)=h•F(h⁻¹g), and its
morphisms apply equivariant additive coefficient maps pointwise. -/
theorem coindMonad_functor :
    (coindMonad.{u, w} G : DiscreteAbelianAction.{u, max u w} G ⥤ _) = coind.{u, w} := rfl

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). For A, the unit η_A:A→C A of the
transported coinduction monad equals the equivariant additive constant-function inclusion ι_A.
Thus each a∈A is sent to g↦a. -/
theorem coindMonad_unit (A : DiscreteAbelianAction.{u, max u w} G) :
    (coindMonad.{u, w} G).η.app A = coindIota.{u, w}.app A :=
  forgetCoindAdjunction_unit_untwist.{u, w} G A

/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). For a coefficient action A, a∈A, and
g∈G, the unit of the diagonal coinduction monad satisfies (η_A(a))(g)=a. The constant function
is regarded as an element of C A with its diagonal action. -/
theorem coindMonad_unit_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (a : underlying A) (g : G) :
    coindFunction.{u, w} A (homToAdd.{u, max u w} ((coindMonad.{u, w} G).η.app A) a) g = a := by
  exact (congrArg (fun f : A ⟶ coind.{u, w}.obj A =>
    coindFunction.{u, w} A (homToAdd.{u, max u w} f a) g)
      (coindMonad_unit.{u, w} G A)).trans (coindIota_apply.{u, w} A a g)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). Let U forget the action, C₀ be its right
adjoint, C diagonal coinduction, u_B:C₀UB≅CB the untwist, and ε_M:U(C₀M)→M evaluation at 1. For
V=C₀UA, multiplication μ_A:C(CA)→CA factors as C(u_A.inv)≫u_V.inv≫C(triv(ε_{UA}))≫u_A.hom. Here
triv(ε_{UA}) is the same additive map between trivial coefficient actions. -/
theorem coindMonad_mul_factorization (A : DiscreteAbelianAction.{u, max u w} G) :
    (coindMonad.{u, w} G).μ.app A =
      coind.{u, w}.map (coindUntwistIso.{u, w} G A).inv ≫
      (coindUntwistIso.{u, w} G
        ((forgetCoindFunctor.{u, w} G).obj ((forget.{u, max u w} G).obj A))).inv ≫
      coind.{u, w}.map (trivialMap.{u, max u w} G
        ((forgetCoindAdjunction.{u, w} G).counit.app ((forget.{u, max u w} G).obj A))) ≫
      (coindUntwistIso.{u, w} G A).hom := by
  change ((coindUntwistNatIso.{u, w} G).inv ◫ (coindUntwistNatIso.{u, w} G).inv).app A ≫
      (forgetCoindFunctor.{u, w} G).map
        ((forgetCoindAdjunction.{u, w} G).counit.app ((forget.{u, max u w} G).obj A)) ≫
      (coindUntwistNatIso.{u, w} G).hom.app A = _
  rw [NatTrans.hcomp_app]
  have h := (coindUntwistNatIso.{u, w} G).inv.naturality
    ((coindUntwistNatIso.{u, w} G).inv.app A)
  have hh := congrArg (fun f =>
    f ≫ (forgetCoindFunctor.{u, w} G).map
      ((forgetCoindAdjunction.{u, w} G).counit.app ((forget.{u, max u w} G).obj A)) ≫
      (coindUntwistNatIso.{u, w} G).hom.app A) h.symm
  exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact, totally disconnected topological group in universe u, with discrete
continuous abelian coefficients in universe W=max(u,w). For a nested continuous coinduced
function F∈C(CA) and g∈G, multiplication μ_A:C(CA)→CA satisfies (μ_A F)(g)=F(g)(g). The outer
and inner evaluations use the same group element, and the result lies in the diagonal
coinduction of A. -/
theorem coindMonad_mul_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (z : underlying (coind.{u, w}.obj (coind.{u, w}.obj A))) (g : G) :
    coindFunction.{u, w} A (homToAdd.{u, max u w} ((coindMonad.{u, w} G).μ.app A) z) g =
      coindFunction.{u, w} A (coindFunction.{u, w} (coind.{u, w}.obj A) z g) g := by
  let L := trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)
  let V := coind.{u, w}.obj L
  let T := trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj V)
  let p : coind.{u, w}.obj (coind.{u, w}.obj A) ⟶ coind.{u, w}.obj V :=
    coind.{u, w}.map (coindUntwistIso.{u, w} G A).inv
  let q : coind.{u, w}.obj V ⟶ coind.{u, w}.obj T :=
    (coindUntwistIso.{u, w} G V).inv
  let r : coind.{u, w}.obj T ⟶ V :=
    coind.{u, w}.map (trivialMap.{u, max u w} G
      ((forgetCoindAdjunction.{u, w} G).counit.app ((forget.{u, max u w} G).obj A)))
  let s : V ⟶ coind.{u, w}.obj A := (coindUntwistIso.{u, w} G A).hom
  let z₁ := homToAdd.{u, max u w} p z
  let z₂ := homToAdd.{u, max u w} q z₁
  let z₃ := homToAdd.{u, max u w} r z₂
  have hf := congrArg
    (fun f : coind.{u, w}.obj (coind.{u, w}.obj A) ⟶ coind.{u, w}.obj A =>
      coindFunction.{u, w} A (homToAdd.{u, max u w} f z) g)
    (coindMonad_mul_factorization.{u, w} G A)
  have hc : coindFunction.{u, w} A (homToAdd.{u, max u w} (p ≫ q ≫ r ≫ s) z) g =
      coindFunction.{u, w} A (homToAdd.{u, max u w} s z₃) g := rfl
  have h₁ := coind_map_apply.{u, w} (coindUntwistIso.{u, w} G A).inv z g
  have h₂ := coindUntwistIso_inv_apply.{u, w} G V z₁ g
  have h₃ := coind_map_apply.{u, w}
    (trivialMap.{u, max u w} G
      ((forgetCoindAdjunction.{u, w} G).counit.app ((forget.{u, max u w} G).obj A))) z₂ g
  have h₄ := forgetCoindAdjunction_counit_apply.{u, w} G
    ((forget.{u, max u w} G).obj A) (coindFunction.{u, w} T z₂ g)
  have ht := congrArg (fun x : underlying T =>
    coindFunction.{u, w} L (show underlying V from x) 1) h₂
  have hs : coindFunction.{u, w} L
      ((V.obj.obj.ρ g⁻¹).asHom.hom (coindFunction.{u, w} V z₁ g)) 1 =
      coindFunction.{u, w} L (coindFunction.{u, w} V z₁ g) g := by
    exact (coind_action_apply.{u, w} L g⁻¹ 1 (coindFunction.{u, w} V z₁ g)).trans
      ((trivialObject_smul.{u, max u w} G ((forget.{u, max u w} G).obj A) g⁻¹ _).trans
        (congrArg (fun t : G => coindFunction.{u, w} L (coindFunction.{u, w} V z₁ g) t)
          (by rw [inv_inv, mul_one])))
  have hp := congrArg (fun x : underlying V => coindFunction.{u, w} L x g) h₁
  have hi := coindUntwistIso_inv_apply.{u, w} G A
    (coindFunction.{u, w} (coind.{u, w}.obj A) z g) g
  have hm : coindFunction.{u, w} L z₃ g =
      (show underlying L from
        g⁻¹ • coindFunction.{u, w} A (coindFunction.{u, w} (coind.{u, w}.obj A) z g) g) :=
    h₃.trans (h₄.trans (ht.trans (hs.trans (hp.trans hi))))
  have hv := coindUntwistIso_hom_apply.{u, w} G A z₃ g
  have hu := congrArg (fun x : underlying L => g • (show underlying A from x)) hm
  exact hf.trans (hc.trans (hv.trans (hu.trans (smul_inv_smul g _))))


end CategoryTheory.DiscreteAbelianAction
