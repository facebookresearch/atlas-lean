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
# The actual forgetful and continuous coinduction adjunction

Continuous coinduction of the existing trivial coefficient has the left-shift
action. Evaluation at one is right adjoint to the actual forgetful functor.
The original diagonal continuous coinduction is recovered by the natural
untwist, which sends the actual adjunction unit to the existing constant
function inclusion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory

namespace CategoryTheory.DiscreteAbelianAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The existing trivial coefficient followed by the existing continuous coinduction. -/
def forgetCoindFunctor : AddCommGrpCat.{max u w} ⥤ DiscreteAbelianAction.{u, max u w} G :=
  trivialFunctor.{u, max u w} G ⋙ coind.{u, w}

/-- Equality in the existing coinduced module is equality of every original function value. -/
theorem coindFunction_ext (A : DiscreteAbelianAction.{u, max u w} G)
    {f h : underlying (coind.{u, w}.obj A)}
    (he : ∀ g : G, coindFunction.{u, w} A f g = coindFunction.{u, w} A h g) : f = h := by
  change (show C(G, underlying A) from f) = (show C(G, underlying A) from h)
  exact ContinuousMap.ext he

/-- Zero has zero value at every original coinduced function coordinate. -/
theorem coindFunction_zero (A : DiscreteAbelianAction.{u, max u w} G) (g : G) :
    coindFunction.{u, w} A (0 : underlying (coind.{u, w}.obj A)) g = 0 := rfl

/-- The original coinduced function coordinates retain the stored addition. -/
theorem coindFunction_add (A : DiscreteAbelianAction.{u, max u w} G)
    (f h : underlying (coind.{u, w}.obj A)) (g : G) :
    coindFunction.{u, w} A (f + h) g = coindFunction.{u, w} A f g +
        coindFunction.{u, w} A h g := rfl

/-- Transpose an actual additive coefficient map using the original inverse orbit. -/
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

/-- The transpose retains its literal inverse-orbit value in the existing coinduced carrier. -/
theorem forgetCoindTranspose_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : (forget.{u, max u w} G).obj A ⟶ M)
    (a : underlying A) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G M)
        (homToAdd.{u, max u w} (forgetCoindTranspose.{u, w} G A M f) a) g =
      f.hom (g⁻¹ • a) := rfl

/-- Evaluate an actual equivariant coinduction arrow at the identity. -/
def forgetCoindEvaluate (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M)) :
    (forget.{u, max u w} G).obj A ⟶ M :=
  AddCommGrpCat.ofHom
    { toFun := fun a => coindFunction.{u, w} (trivialObject.{u, max u w} G M)
        (homToAdd.{u, max u w} f a) 1
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun a b => by rw [map_add]; rfl }

/-- Evaluation retains the literal value of the actual equivariant arrow. -/
theorem forgetCoindEvaluate_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M))
    (a : underlying A) :
    (forgetCoindEvaluate.{u, w} G A M f).hom a =
      coindFunction.{u, w} (trivialObject.{u, max u w} G M) (homToAdd.{u, max u w} f a) 1 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Equivariance identifies every coordinate with identity evaluation on an inverse orbit. -/
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
/-- Two arrows into the actual coinduced object agree if all their function values agree. -/
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
/-- Evaluating the literal transpose recovers the original additive arrow. -/
theorem forgetCoindEvaluate_transpose (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : (forget.{u, max u w} G).obj A ⟶ M) :
    forgetCoindEvaluate.{u, w} G A M (forgetCoindTranspose.{u, w} G A M f) = f := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  rw [forgetCoindEvaluate_apply.{u, w}, forgetCoindTranspose_apply.{u, w}, inv_one, one_smul]

set_option backward.isDefEq.respectTransparency.types false in
/-- Transposing identity evaluation recovers the same actual equivariant arrow. -/
theorem forgetCoindTranspose_evaluate (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) (f : A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M)) :
    forgetCoindTranspose.{u, w} G A M (forgetCoindEvaluate.{u, w} G A M f) = f := by
  apply coindHom_ext.{u, w} G A (trivialObject.{u, max u w} G M)
  intro a g
  rw [forgetCoindTranspose_apply.{u, w}, forgetCoindEvaluate_apply.{u, w}]
  exact forgetCoindEquivariantValue.{u, w} G A M f a g

/-- The inverse-orbit transpose and evaluation at one form the actual Hom equivalence. -/
def forgetCoindHomEquiv (A : DiscreteAbelianAction.{u, max u w} G)
    (M : AddCommGrpCat.{max u w}) :
    ((forget.{u, max u w} G).obj A ⟶ M) ≃
        (A ⟶ coind.{u, w}.obj (trivialObject.{u, max u w} G M)) where
  toFun := forgetCoindTranspose.{u, w} G A M
  invFun := forgetCoindEvaluate.{u, w} G A M
  left_inv := forgetCoindEvaluate_transpose.{u, w} G A M
  right_inv := forgetCoindTranspose_evaluate.{u, w} G A M

/-- Forgetting is left adjoint to continuous coinduction of the actual trivial coefficient. -/
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

/-- The actual counit evaluates the original continuous function at one. -/
theorem forgetCoindAdjunction_counit_apply (M : AddCommGrpCat.{max u w})
    (f : underlying (coind.{u, w}.obj (trivialObject.{u, max u w} G M))) :
    (forgetCoindAdjunction.{u, w} G).counit.app M f =
      coindFunction.{u, w} (trivialObject.{u, max u w} G M) f 1 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual unit has the original inverse-orbit function. -/
theorem forgetCoindAdjunction_unit_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (a : underlying A) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))
      (homToAdd.{u, max u w} ((forgetCoindAdjunction.{u, w} G).unit.app A) a) g = g⁻¹ • a := rfl

/-- The forward untwist as an additive map of the original continuous function spaces. -/
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

/-- The inverse untwist is additive on these same continuous function spaces. -/
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
/-- The forward untwist on the two existing coinduced coefficients. -/
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

/-- Every forward coordinate uses the coefficient action at that same group element. -/
theorem coindUntwistHom_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying
        (coind.{u, w}.obj (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)))) (g : G) :
    coindFunction.{u, w} A (homToAdd.{u, max u w} (coindUntwistHom.{u, w} G A) f) g =
      g • (show underlying A from
        coindFunction.{u, w} (trivialObject.{u, max u w} G
            ((forget.{u, max u w} G).obj A)) f g) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse untwist on the same original coinduced coefficients. -/
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
/-- Every inverse coordinate uses the same original inverse action. -/
theorem coindUntwistInv_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying (coind.{u, w}.obj A)) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))
      (homToAdd.{u, max u w} (coindUntwistInv.{u, w} G A) f) g =
        (show underlying (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) from
          g⁻¹ • coindFunction.{u, w} A f g) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Untwist left shift into the existing diagonal coinduction, with its actual inverse. -/
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

/-- The isomorphism has the named actual forward untwist on every coordinate. -/
theorem coindUntwistIso_hom_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying
        (coind.{u, w}.obj (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)))) (g : G) :
    coindFunction.{u, w} A (homToAdd.{u, max u w} (coindUntwistIso.{u, w} G A).hom f) g =
      g • (show underlying A from
        coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) f g) :=
  coindUntwistHom_apply.{u, w} G A f g

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism has the named actual inverse untwist on every coordinate. -/
theorem coindUntwistIso_inv_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (f : underlying (coind.{u, w}.obj A)) (g : G) :
    coindFunction.{u, w} (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A))
      (homToAdd.{u, max u w} (coindUntwistIso.{u, w} G A).inv f) g =
        (show underlying (trivialObject.{u, max u w} G ((forget.{u, max u w} G).obj A)) from
          g⁻¹ • coindFunction.{u, w} A f g) :=
  coindUntwistInv_apply.{u, w} G A f g

set_option backward.isDefEq.respectTransparency.types false in
/-- Untwisting is natural for every actual equivariant additive coefficient arrow. -/
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
/-- The actual unit untwists to the existing constant-function inclusion. -/
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

/-- Evaluation at one is unchanged by the actual untwist. -/
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
