/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Action.Trivial
public import MathlibExt.CategoryTheory.Action.DiscreteTopRep
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Forgetting and continuous coinduction of discrete coefficients

Let G be a compact totally disconnected topological group in universe u, with coefficient groups
in W=max(u,w). Diagonal coinduction C(A) consists of continuous functions G→U(A), with
(h•F)(g)=h•F(h⁻¹g). Applied to a trivial coefficient M, C₀(M) has the left-shift action
F(g)↦F(h⁻¹g).

The forgetful U is left adjoint to C₀. An additive f:U(A)→M transposes to a↦[g↦f(g⁻¹a)], and an
equivariant map into C₀(M) evaluates at identity to an additive map. The counit is evaluation at
identity; the unit is the inverse-orbit function. Multiplying the value at g by g gives a
natural isomorphism C₀(U(A))≅C(A), with inverse multiplying by g⁻¹. This untwist sends the unit
to the constant-function inclusion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory

namespace CategoryTheory.DiscreteAbelianAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
an abelian group M in W, C₀(M) is the discrete action of continuous functions G→M with
(h•F)(g)=F(h⁻¹g). A coefficient map acts by postcomposition. -/
def forgetCoindFunctor : AddCommGrpCat.{max u w} ⥤ DiscreteAbelianAction.{u, max u w} G :=
  trivialFunctor.{u, max u w} G ⋙ coind.{u, w}

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A a discrete coefficient action and F,H∈C(A), if F(g)=H(g) for every g∈G then F=H. The
underlying elements are continuous maps. -/
theorem coindFunction_ext (A : DiscreteAbelianAction.{u, max u w} G)
    {f h : underlying (coind.{u, w}.obj A)}
    (he : ∀ g : G, coindFunction.{u, w} A f g = coindFunction.{u, w} A h g) : f = h := by
  change (show C(G, underlying A) from f) = (show C(G, underlying A) from h)
  exact ContinuousMap.ext he

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
a coefficient action A and g∈G, the zero function in C(A) has value zero at g. -/
theorem coindFunction_zero (A : DiscreteAbelianAction.{u, max u w} G) (g : G) :
    coindFunction.{u, w} A (0 : underlying (coind.{u, w}.obj A)) g = 0 := rfl

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A and F,H∈C(A), (F+H)(g)=F(g)+H(g) for every g∈G. -/
theorem coindFunction_add (A : DiscreteAbelianAction.{u, max u w} G)
    (f h : underlying (coind.{u, w}.obj A)) (g : G) :
    coindFunction.{u, w} A (f + h) g = coindFunction.{u, w} A f g +
        coindFunction.{u, w} A h g := rfl

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A a discrete action, M an abelian group in W and f:U(A)→M additive, its transpose A→C₀(M) sends
a to the continuous function g↦f(g⁻¹•a). This function family is additive and G-equivariant. -/
def forgetCoindTranspose (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : (forget.{u, max u w} G).obj A ⟶ M) :
    A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M) := by
  let Z := trivialObject.{u, max u w} G M
  let T := coind.{u, w}.obj Z
  let fA : underlying A →+ underlying Z :=
    { toFun := fun a => (show underlying Z from f.hom a)
      map_zero' := f.hom.map_zero
      map_add' := fun a b => f.hom.map_add a b }
  let φ : underlying A →+ underlying T :=
    { toFun := fun a =>
        (show underlying T from
          ({ toFun := fun g => fA (g⁻¹ • a)
             continuous_toFun := by
               have hf : Continuous (fun a : underlying A =>
                   fA a) := continuous_of_discreteTopology
               exact hf.comp ((continuous_action A).comp
                 (continuous_inv.prodMk continuous_const)) } : C(G, underlying Z)))
      map_zero' := by
        apply coindFunction_ext.{u, w} G Z
        intro g
        change fA (g⁻¹ • (0 : underlying A)) = 0
        exact (congrArg fA (smul_zero g⁻¹)).trans fA.map_zero
      map_add' := by
        intro a b
        apply coindFunction_ext.{u, w} G Z
        intro g
        change fA (g⁻¹ • (a + b)) = fA (g⁻¹ • a) + fA (g⁻¹ • b)
        exact (congrArg fA (smul_add g⁻¹ a b)).trans (fA.map_add _ _) }
  exact ofAddHom.{u, max u w} ⟨φ, fun h a => by
    apply coindFunction_ext.{u, w} G Z
    intro g
    change fA (g⁻¹ • (h • a)) = fA ((h⁻¹ * g)⁻¹ • a)
    rw [smul_smul, mul_inv_rev, inv_inv]⟩

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
f:U(A)→M, a∈A and g∈G, the transpose satisfies transpose(f)(a)(g)=f(g⁻¹•a). -/
theorem forgetCoindTranspose_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : (forget.{u, max u w} G).obj A ⟶ M)
    (a : underlying A) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G M)
        (homToAdd.{u, max u w} (forgetCoindTranspose.{u, w} G A M f) a) g =
      f.hom (g⁻¹ • a) := rfl

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
an equivariant additive h:A→C₀(M), identity evaluation gives the additive map U(A)→M, a↦h(a)(1). -/
def forgetCoindEvaluate (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M)) :
    (forget.{u, max u w} G).obj A ⟶ M :=
  AddCommGrpCat.ofHom
    { toFun := fun a => coindFunction.{u, w} (trivialObject.{u, max u w} G M)
        (homToAdd.{u, max u w} f a) 1
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun a b => by rw [map_add]; rfl }

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
h:A→C₀(M) and a∈A, evaluate(h)(a)=h(a)(1). This is evaluation in the underlying
continuous-function group. -/
theorem forgetCoindEvaluate_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M))
    (a : underlying A) :
    (forgetCoindEvaluate.{u, w} G A M f).hom a =
      coindFunction.{u, w} (trivialObject.{u, max u w} G M) (homToAdd.{u, max u w} f a) 1 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
an action morphism h:A→C₀(M), a∈A and g∈G, h(g⁻¹•a)(1)=h(a)(g). The target has trivial
coefficient action and left shift. -/
theorem forgetCoindEquivariantValue (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M))
    (a : underlying A) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G M) (homToAdd.{u, max u w} f (g⁻¹ • a)) 1 =
      coindFunction.{u, w} (trivialObject.{u, max u w} G M) (homToAdd.{u, max u w} f a) g := by
  have h := congrArg
    (fun z : underlying (coind.{u, w}.obj (trivialObject.{u, max u w} G M)) =>
      coindFunction.{u, w} (trivialObject.{u, max u w} G M) z 1)
    (homToAdd_equivariant.{u, max u w} f g⁻¹ a)
  have hc := coind_action_apply.{u, w} (trivialObject.{u, max u w} G M) g⁻¹ 1
      (homToAdd.{u, max u w} f a)
  have ht := trivialObject_smul.{u, max u w} G M g⁻¹
    (coindFunction.{u, w} (trivialObject.{u, max u w} G M) (homToAdd.{u, max u w} f a)
        ((g⁻¹)⁻¹ * 1))
  exact h.trans (hc.trans (ht.trans (by rw [inv_inv, mul_one])))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
action morphisms f,h:A→C(B), equality f(a)(g)=h(a)(g) for every a∈A,g∈G implies f=h. -/
theorem coindHom_ext (A B : DiscreteAbelianAction.{u, max u w} G)
    {f h : A ⟶ coind.{u, w}.obj B}
    (he : ∀ (a : underlying A) (g : G),
      coindFunction.{u, w} B (homToAdd.{u, max u w} f a) g =
          coindFunction.{u, w} B (homToAdd.{u, max u w} h a) g) : f = h := by
  apply (homEquiv.{u, max u w} A (coind.{u, w}.obj B)).injective
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro a
  exact coindFunction_ext.{u, w} G B (he a)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
f:U(A)→M additive, evaluate(transpose(f))=f. At identity the inverse orbit is a itself. -/
theorem forgetCoindEvaluate_transpose (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : (forget.{u, max u w} G).obj A ⟶ M) :
    forgetCoindEvaluate.{u, w} G A M (forgetCoindTranspose.{u, w} G A M f) = f := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  rw [forgetCoindEvaluate_apply.{u, w}, forgetCoindTranspose_apply.{u, w}, inv_one, one_smul]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
h:A→C₀(M), transpose(evaluate(h))=h. The equality follows from h(g⁻¹•a)(1)=h(a)(g) at every
coordinate. -/
theorem forgetCoindTranspose_evaluate (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M)) :
    forgetCoindTranspose.{u, w} G A M (forgetCoindEvaluate.{u, w} G A M f) = f := by
  apply coindHom_ext.{u, w} G A (trivialObject.{u, max u w} G M)
  intro a g
  rw [forgetCoindTranspose_apply.{u, w}, forgetCoindEvaluate_apply.{u, w}]
  exact forgetCoindEquivariantValue.{u, w} G A M f a g

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction.
There is a bijection Hom_Ab(U(A),M)≅Hom_G(A,C₀(M)). Its forward map is f↦[a↦(g↦f(g⁻¹a))] and its
inverse is h↦[a↦h(a)(1)]. -/
def forgetCoindHomEquiv (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) :
    ((forget.{u, max u w} G).obj A ⟶ M) ≃
        (A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M)) where
  toFun := forgetCoindTranspose.{u, w} G A M
  invFun := forgetCoindEvaluate.{u, w} G A M
  left_inv := forgetCoindEvaluate_transpose.{u, w} G A M
  right_inv := forgetCoindTranspose_evaluate.{u, w} G A M

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. The
inverse-orbit Hom bijections are natural in A and M and define U⊣C₀. Its unit is the
inverse-orbit inclusion and its counit evaluates at identity. -/
def forgetCoindAdjunction : forget.{u, max u w} G ⊣ forgetCoindFunctor.{u, w} G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := forgetCoindHomEquiv.{u, w} G
      homEquiv_naturality_left_symm := fun {A A' M} f g => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro a
        rfl
      homEquiv_naturality_right := fun {A M N} f g => by
        apply (forget.{u, max u w} G).map_injective
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro a
        simp only [forget_map, homToAdd_comp]
        apply coindFunction_ext.{u, w} G (trivialObject.{u, max u w} G N)
        intro h
        rfl }

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
an abelian coefficient M and F∈C₀(M), the counit U(C₀(M))→M sends F to F(1). -/
theorem forgetCoindAdjunction_counit_apply (M : AddCommGrpCat.{max u w})
    (f : underlying (coind.{u, w}.obj (trivialObject.{u, max u w} G M))) :
    (forgetCoindAdjunction.{u, w} G).counit.app M f =
      coindFunction.{u, w} (trivialObject.{u, max u w} G M) f 1 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
a discrete action A, a∈A and g∈G, the unit A→C₀(U(A)) satisfies η_A(a)(g)=g⁻¹•a. -/
theorem forgetCoindAdjunction_unit_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (a : underlying A) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))
      (homToAdd.{u, max u w} ((forgetCoindAdjunction.{u, w} G).unit.app A) a) g = g⁻¹ • a := rfl

/-- Let G be a topological group in universe u and A a discrete continuous abelian action with
coefficient group in W=max(u,w), for an independent height w. The additive map from continuous
functions G→U(A) with trivial coefficient interpretation to those with A's coefficient
interpretation sends F to g↦g•F(g). Joint continuity of the action makes the result continuous. -/
def coindUntwistAddHom (A : DiscreteAbelianAction.{u, max u w} G) :
    C(G, underlying (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))) →+
        C(G, underlying A) where
  toFun f :=
    { toFun := fun g => g • (show underlying A from f g)
      continuous_toFun := by
        have hc :
            Continuous (fun z : underlying
              (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) =>
            (show underlying A from z)) := continuous_of_discreteTopology
        exact (continuous_action A).comp (continuous_id.prodMk (hc.comp f.continuous)) }
  map_zero' := by
    apply ContinuousMap.ext
    intro g
    change g • (0 : underlying A) = 0
    exact smul_zero g
  map_add' f h := by
    apply ContinuousMap.ext
    intro g
    change g • ((show underlying A from f g) + (show underlying A from h g)) = _
    exact smul_add g _ _

/-- Let G be a topological group in universe u and A a discrete continuous abelian action with
coefficient group in W=max(u,w), with w independent. The additive function-space map
F↦[g↦g⁻¹•F(g)] reverses the coordinate-action untwist. Group inversion and the continuous action
preserve continuity. -/
def coindUntwistInverseAddHom (A : DiscreteAbelianAction.{u, max u w} G) :
    C(G, underlying A) →+ C(G,
        underlying (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))) where
  toFun f :=
    { toFun := fun g =>
        (show underlying (trivialObject.{u, max u w} G
          ((forget.{u, max u w} G).obj A)) from g⁻¹ • f g)
      continuous_toFun := by
        have hc : Continuous (fun z : underlying A =>
            (show underlying (trivialObject.{u, max u w} G
                ((forget.{u, max u w} G).obj A)) from z)) :=
          continuous_of_discreteTopology
        exact hc.comp ((continuous_action A).comp (continuous_inv.prodMk f.continuous)) }
  map_zero' := by
    apply ContinuousMap.ext
    intro g
    change (g⁻¹ • (0 : underlying A) : underlying A) = 0
    exact smul_zero g⁻¹
  map_add' f h := by
    apply ContinuousMap.ext
    intro g
    change (g⁻¹ • (f g + h g) : underlying A) = _
    exact smul_add g⁻¹ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A, the map C₀(U(A))→C(A) sends F to g↦g•F(g). It is additive, continuous and equivariant between
the left-shift and diagonal actions. -/
def coindUntwistHom (A : DiscreteAbelianAction.{u, max u w} G) :
    coind.{u, w}.obj (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) ⟶
        coind.{u, w}.obj A := by
  let Z := trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)
  let h : underlying (coind.{u, w}.obj Z) →+ underlying (coind.{u, w}.obj A) := by
    change C(G, underlying Z) →+ C(G, underlying A)
    exact coindUntwistAddHom.{u, w} G A
  exact ofAddHom.{u, max u w} ⟨h, fun a f => by
    apply coindFunction_ext.{u, w} G A
    intro g
    change g • (show underlying A from coindFunction.{u, w} Z f (a⁻¹ * g)) =
      a • ((a⁻¹ * g) • (show underlying A from coindFunction.{u, w} Z f (a⁻¹ * g)))
    rw [smul_smul, mul_inv_cancel_left]⟩

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A, F∈C₀(U(A)) and g∈G, the equivariant untwist map has value untwist(F)(g)=g•F(g). -/
theorem coindUntwistHom_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying
        (coind.{u, w}.obj (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)))) (g : G) :
    coindFunction.{u, w} A (homToAdd.{u, max u w} (coindUntwistHom.{u, w} G A) f) g =
      g • (show underlying A from
        coindFunction.{u, w} (trivialObject.{u, max u w} G
            ((forget.{u, max u w} G).obj A)) f g) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A, the map C(A)→C₀(U(A)) sends F to g↦g⁻¹•F(g). It is equivariant for the diagonal source and
left-shift target actions. -/
def coindUntwistInv (A : DiscreteAbelianAction.{u, max u w} G) :
    coind.{u, w}.obj A ⟶ coind.{u, w}.obj
        (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) := by
  let Z := trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)
  let i : underlying (coind.{u, w}.obj A) →+ underlying (coind.{u, w}.obj Z) := by
    change C(G, underlying A) →+ C(G, underlying Z)
    exact coindUntwistInverseAddHom.{u, w} G A
  exact ofAddHom.{u, max u w} ⟨i, fun a f => by
    apply coindFunction_ext.{u, w} G Z
    intro g
    change g⁻¹ • (a • coindFunction.{u, w} A f (a⁻¹ * g)) =
      (a⁻¹ * g)⁻¹ • coindFunction.{u, w} A f (a⁻¹ * g)
    rw [smul_smul, mul_inv_rev, inv_inv]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A, F∈C(A) and g∈G, inverseUntwist(F)(g)=g⁻¹•F(g). -/
theorem coindUntwistInv_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying (coind.{u, w}.obj A)) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))
      (homToAdd.{u, max u w} (coindUntwistInv.{u, w} G A) f) g =
        (show underlying (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) from
          g⁻¹ • coindFunction.{u, w} A f g) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A, the isomorphism u_A:C₀(U(A))≅C(A) has forward formula u_A(F)(g)=g•F(g) and inverse
u_A^{-1}(H)(g)=g⁻¹•H(g). The group action identities give both inverse laws. -/
def coindUntwistIso (A : DiscreteAbelianAction.{u, max u w} G) :
    coind.{u, w}.obj (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) ≅
        coind.{u, w}.obj A where
  hom := coindUntwistHom.{u, w} G A
  inv := coindUntwistInv.{u, w} G A
  hom_inv_id := by
    apply coindHom_ext.{u, w} G (coind.{u, w}.obj
        (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)))
      (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))
    intro f g
    simp only [homToAdd_comp, homToAdd_id, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
    rw [coindUntwistInv_apply.{u, w}, coindUntwistHom_apply.{u, w}]
    exact inv_smul_smul g (show underlying A from
      coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) f g)
  inv_hom_id := by
    apply coindHom_ext.{u, w} G (coind.{u, w}.obj A) A
    intro f g
    simp only [homToAdd_comp, homToAdd_id, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
    rw [coindUntwistHom_apply.{u, w}, coindUntwistInv_apply.{u, w}]
    exact smul_inv_smul g (coindFunction.{u, w} A f g)

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
the canonical isomorphism u_A and F∈C₀(U(A)), (u_A.hom F)(g)=g•F(g) for every g. This identifies
its forward component with the equivariant untwist. -/
theorem coindUntwistIso_hom_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying
        (coind.{u, w}.obj (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)))) (g : G) :
    coindFunction.{u, w} A (homToAdd.{u, max u w} (coindUntwistIso.{u, w} G A).hom f) g =
      g • (show underlying A from
        coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) f g) :=
  coindUntwistHom_apply.{u, w} G A f g

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
H∈C(A), (u_A.inv H)(g)=g⁻¹•H(g). This is the inverse component of the left-shift/diagonal
comparison. -/
theorem coindUntwistIso_inv_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying (coind.{u, w}.obj A)) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))
      (homToAdd.{u, max u w} (coindUntwistIso.{u, w} G A).inv f) g =
        (show underlying (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) from
          g⁻¹ • coindFunction.{u, w} A f g) :=
  coindUntwistInv_apply.{u, w} G A f g

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. The
isomorphisms u_A:C₀(U(A))≅C(A) form a natural isomorphism U⋙C₀≅C. For f:A→B,
C₀(U(f))≫u_B.hom=u_A.hom≫C(f), by equivariance of f on g•F(g). -/
def coindUntwistNatIso : forget.{u, max u w} G ⋙ forgetCoindFunctor.{u, w} G ≅ coind.{u, w} :=
  NatIso.ofComponents (coindUntwistIso.{u, w} G) (fun f => by
    apply (forget.{u, max u w} G).map_injective
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    simp only [forget_map, homToAdd_comp]
    apply coindFunction_ext.{u, w} G _
    intro g
    exact (homToAdd_equivariant.{u, max u w} f g _).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
A, η_A≫u_A.hom=ι_A, where η_A(a)(g)=g⁻¹a and ι_A(a) is the constant function with value a in
diagonal coinduction C(A). -/
theorem forgetCoindAdjunction_unit_untwist (A : DiscreteAbelianAction.{u, max u w} G) :
    (forgetCoindAdjunction.{u, w} G).unit.app A ≫ (coindUntwistIso.{u, w} G A).hom =
      coindIota.{u, w}.app A := by
  apply coindHom_ext.{u, w} G A A
  intro a g
  simp only [homToAdd_comp, AddMonoidHom.comp_apply]
  have h₁ := coindUntwistIso_hom_apply.{u, w} G A
    (homToAdd.{u, max u w} ((forgetCoindAdjunction.{u, w} G).unit.app A) a) g
  have h₂ := congrArg (fun x : underlying A => g • x)
    (forgetCoindAdjunction_unit_apply.{u, w} G A a g)
  exact h₁.trans (h₂.trans ((smul_inv_smul g a).trans
    (coindIota_apply.{u, w} A a g).symm))

/-- Let G be a compact totally disconnected topological group in universe u and W=max(u,w) a
coefficient universe with w independent. Write U for the forgetful functor to abelian groups in
W, C for diagonal continuous coinduction and C₀(M)=C(trivial M) for left-shift coinduction. For
F∈C₀(U(A)), u_A(F)(1)=F(1). The identity element acts trivially on the coefficient A. -/
theorem coindUntwistIso_eval_one (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying
        (coind.{u, w}.obj (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)))) :
    coindFunction.{u, w} A (homToAdd.{u, max u w} (coindUntwistIso.{u, w} G A).hom f) 1 =
      (show underlying A from
        coindFunction.{u, w} (trivialObject.{u, max u w} G
            ((forget.{u, max u w} G).obj A)) f 1) := by
  rw [coindUntwistIso_hom_apply.{u, w}]
  exact one_smul G _

end CategoryTheory.DiscreteAbelianAction
