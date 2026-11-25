/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.LieModuleCat.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic.Abel

/-!
# Right modules over a Lie algebra

The bilinear action satisfies
`m · [x, y] = (m · x) · y - (m · y) · x`.
Negating it gives a left Lie module with `[x, m] = -(m · x)`; the inverse
construction negates a left action. Maps over a Lie algebra homomorphism are
linear maps that preserve the corresponding actions.

The ring, Lie algebra, and coefficient carrier have independent universes.
Each left action is stored on its bundled module object.
-/

@[expose] public section

open CategoryTheory
attribute [local instance] LieRing.ofAssociativeRing

universe w w' w'' v v' v'' u

/-- An right module over a Lie algebra, with bilinear action and its right law. -/
structure RightLieModuleCat (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L] where
  /-- The original coefficient carrier. -/
  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [moduleStructure : Module R carrier]
  /-- Evaluation of this endomorphism at `m` is the right action `m · x`. -/
  action : L →ₗ[R] Module.End R carrier
  /-- The bracket acts by the right commutator, with the action order retained. -/
  right_lie : ∀ (x y : L) (m : carrier),
    action ⁅x, y⁆ m = action y (action x m) - action x (action y m)

attribute [instance] RightLieModuleCat.addCommGroup RightLieModuleCat.moduleStructure

namespace RightLieModuleCat

variable {R : Type u} [CommRing R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]
variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

instance instCoeSort : CoeSort (RightLieModuleCat.{w} R L) (Type w) := ⟨carrier⟩

/-- Bundle an existing bilinear right action, without extending it to an enveloping algebra. -/
def of (M : Type w) [AddCommGroup M] [Module R M]
    (a : L →ₗ[R] Module.End R M)
    (ha : ∀ (x y : L) (m : M), a ⁅x, y⁆ m = a y (a x m) - a x (a y m)) :
    RightLieModuleCat.{w} R L where
  carrier := M
  action := a
  right_lie := ha

/-- Right-order notation for the action. -/
def act (M : RightLieModuleCat.{w} R L) (m : M) (x : L) : M := M.action x m

@[simp]
theorem act_lie (M : RightLieModuleCat.{w} R L) (m : M) (x y : L) :
    act M m ⁅x, y⁆ = act M (act M m x) y - act M (act M m y) x :=
  M.right_lie x y m

/-- Negating a right action constructs the native left Lie-ring-module data. -/
@[instance_reducible]
def negativeLieRingModule (M : RightLieModuleCat.{w} R L) : LieRingModule L M where
  bracket x m := -(M.action x m)
  add_lie x y m := by
    change -(M.action (x + y) m) = -(M.action x m) + -(M.action y m)
    rw [M.action.map_add, LinearMap.add_apply, neg_add]
  lie_add x m n := by
    change -(M.action x (m + n)) = -(M.action x m) + -(M.action x n)
    rw [(M.action x).map_add, neg_add]
  leibniz_lie x y m := by
    change -(M.action x (-(M.action y m))) =
      -(M.action ⁅x, y⁆ m) + -(M.action y (-(M.action x m)))
    rw [(M.action x).map_neg, (M.action y).map_neg, neg_neg, neg_neg,
      M.right_lie x y m]
    abel

/-- The native left coefficient object has the original carrier and negative right action. -/
@[implicit_reducible]
def toLeft (M : RightLieModuleCat.{w} R L) : LieModuleCat.{w} R L := by
  letI : LieRingModule L M := negativeLieRingModule M
  letI : LieModule R L M :=
    { smul_lie := fun r x m => by
        change -(M.action (r • x) m) = r • -(M.action x m)
        rw [M.action.map_smul, LinearMap.smul_apply, smul_neg]
      lie_smul := fun r x m => by
        change -(M.action x (r • m)) = r • -(M.action x m)
        rw [(M.action x).map_smul, smul_neg] }
  exact LieModuleCat.of R L M

@[simp]
theorem toLeft_carrier (M : RightLieModuleCat.{w} R L) :
    (toLeft M).carrier = M.carrier := rfl

/-- The left action is the negative right action, not an additional input. -/
@[simp]
theorem toLeft_lie (M : RightLieModuleCat.{w} R L) (x : L) (m : M) :
    @Bracket.bracket L (toLeft M) inferInstance x m = -(M.action x m) := rfl

/-- Negating a native left representation gives right Lie coefficients. -/
def fromLeft (M : LieModuleCat.{w} R L) : RightLieModuleCat.{w} R L where
  carrier := M
  action := -(LieModule.toEnd R L M).toLinearMap
  right_lie x y m := by
    change -⁅⁅x, y⁆, m⁆ = -⁅y, -⁅x, m⁆⁆ - (-⁅x, -⁅y, m⁆⁆)
    rw [lie_neg, lie_neg, neg_neg, neg_neg, leibniz_lie]
    abel
    rw [neg_one_smul, ← lie_skew y x, neg_lie]

/-- The right action constructed from a left module is its negative left action. -/
@[simp]
theorem fromLeft_action (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    (fromLeft M).action x m = -⁅x, m⁆ := rfl

/-- Compatible coefficient maps over a Lie map form a native linear submodule. -/
def homOverSubmodule (f : L →ₗ⁅R⁆ L')
    (M : RightLieModuleCat.{w} R L) (N : RightLieModuleCat.{w'} R L') :
    Submodule R (M →ₗ[R] N) where
  carrier := {g | ∀ (x : L) (m : M), g (M.action x m) = N.action (f x) (g m)}
  zero_mem' := by
    intro x m
    change 0 = N.action (f x) 0
    exact (N.action (f x)).map_zero.symm
  add_mem' := by
    intro g h hg hh x m
    change g (M.action x m) + h (M.action x m) = N.action (f x) (g m + h m)
    rw [hg x m, hh x m, (N.action (f x)).map_add]
  smul_mem' := by
    intro r g hg x m
    change r • g (M.action x m) = N.action (f x) (r • g m)
    rw [hg x m, (N.action (f x)).map_smul]

/-- An right coefficient map compatible with the specified Lie map. -/
abbrev HomOver (f : L →ₗ⁅R⁆ L')
    (M : RightLieModuleCat.{w} R L) (N : RightLieModuleCat.{w'} R L') :=
  ↥(homOverSubmodule f M N)

namespace HomOver

/-- The original linear map underlying a compatible right coefficient map. -/
abbrev toLinearMap {f : L →ₗ⁅R⁆ L'} {M : RightLieModuleCat.{w} R L}
    {N : RightLieModuleCat.{w'} R L'} (g : HomOver f M N) : M →ₗ[R] N := g.val

theorem map_action {f : L →ₗ⁅R⁆ L'} {M : RightLieModuleCat.{w} R L}
    {N : RightLieModuleCat.{w'} R L'} (g : HomOver f M N) (x : L) (m : M) :
    g.toLinearMap (M.action x m) = N.action (f x) (g.toLinearMap m) := g.property x m

/-- Compose the coefficient maps and the Lie maps. -/
def comp {f : L →ₗ⁅R⁆ L'} {h : L' →ₗ⁅R⁆ L''}
    {M : RightLieModuleCat.{w} R L} {N : RightLieModuleCat.{w'} R L'}
    {P : RightLieModuleCat.{w''} R L''} (k : HomOver h N P) (g : HomOver f M N) :
    HomOver (h.comp f) M P :=
  ⟨k.toLinearMap.comp g.toLinearMap, by
    intro x m
    change k.toLinearMap (g.toLinearMap (M.action x m)) =
      P.action (h (f x)) (k.toLinearMap (g.toLinearMap m))
    rw [g.map_action x m, k.map_action (f x) (g.toLinearMap m)]⟩

@[simp]
theorem comp_apply {f : L →ₗ⁅R⁆ L'} {h : L' →ₗ⁅R⁆ L''}
    {M : RightLieModuleCat.{w} R L} {N : RightLieModuleCat.{w'} R L'}
    {P : RightLieModuleCat.{w''} R L''} (k : HomOver h N P) (g : HomOver f M N) (m : M) :
    (comp k g).toLinearMap m = k.toLinearMap (g.toLinearMap m) := rfl

end HomOver

instance instCategory : Category (RightLieModuleCat.{w} R L) where
  Hom M N := HomOver (LieHom.id : L →ₗ⁅R⁆ L) M N
  id M := ⟨LinearMap.id, fun _ _ => rfl⟩
  comp {M N P} g h := ⟨h.toLinearMap.comp g.toLinearMap, by
    intro x m
    change h.toLinearMap (g.toLinearMap (M.action x m)) =
      P.action x (h.toLinearMap (g.toLinearMap m))
    rw [g.map_action x m, h.map_action (LieHom.id x) (g.toLinearMap m)]
    rfl⟩
  id_comp g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    rfl
  comp_id g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    rfl
  assoc g h k := by
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    rfl

@[ext]
theorem hom_ext {M N : RightLieModuleCat.{w} R L} {f g : M ⟶ N}
    (h : ∀ m : M, f.toLinearMap m = g.toLinearMap m) : f = g := by
  apply Subtype.ext
  exact LinearMap.ext h

instance instPreadditive : Preadditive (RightLieModuleCat.{w} R L) where
  homGroup M N := inferInstanceAs (AddCommGroup (HomOver (LieHom.id : L →ₗ⁅R⁆ L) M N))
  add_comp M N P f g h := by
    apply hom_ext
    intro m
    exact h.toLinearMap.map_add (f.toLinearMap m) (g.toLinearMap m)
  comp_add M N P f g h := by
    apply hom_ext
    intro m
    rfl

instance homModule (M N : RightLieModuleCat.{w} R L) : Module R (M ⟶ N) :=
  inferInstanceAs (Module R (HomOver (LieHom.id : L →ₗ⁅R⁆ L) M N))

instance instLinear : Linear R (RightLieModuleCat.{w} R L) where
  homModule := homModule
  smul_comp M N P r f g := by
    apply hom_ext
    intro m
    exact g.toLinearMap.map_smul r (f.toLinearMap m)
  comp_smul M N P r f g := by
    apply hom_ext
    intro m
    rfl

/-- A right coefficient map becomes a native map between the left modules. -/
def toLeftMap {M N : RightLieModuleCat.{w} R L} (g : M ⟶ N) :
    toLeft M →ₗ⁅R,L⁆ toLeft N where
  toLinearMap := g.toLinearMap
  map_lie' := by
    intro x m
    change g.toLinearMap (-(M.action x m)) = -(N.action x (g.toLinearMap m))
    rw [g.toLinearMap.map_neg]
    exact congrArg Neg.neg (g.map_action x m)

theorem toLeftMap_apply {M N : RightLieModuleCat.{w} R L} (g : M ⟶ N) (m : M) :
    toLeftMap g m = g.toLinearMap m := rfl

/-- Negation of the right action is functorial in the coefficient morphisms. -/
def toLeftFunctor : RightLieModuleCat.{w} R L ⥤ LieModuleCat.{w} R L where
  obj := toLeft
  map g := toLeftMap g
  map_id M := by
    apply LieModuleHom.ext
    intro m
    rfl
  map_comp g h := by
    apply LieModuleHom.ext
    intro m
    rfl

instance toLeftFunctor_additive : (toLeftFunctor (R := R) (L := L)).Additive where
  map_add {M N} g h := by
    apply LieModuleHom.ext
    intro m
    rfl

instance toLeftFunctor_linear : (toLeftFunctor (R := R) (L := L)).Linear R where
  map_smul {M N} g r := by
    apply LieModuleHom.ext
    intro m
    rfl

/-- Trivial right coefficients have the zero action. -/
def trivial (M : Type w) [AddCommGroup M] [Module R M] : RightLieModuleCat.{w} R L where
  carrier := M
  action := 0
  right_lie x y m := by simp

@[simp]
theorem trivial_action (M : Type w) [AddCommGroup M] [Module R M] (x : L) (m : M) :
    (trivial (R := R) (L := L) M).action x m = 0 := rfl

end RightLieModuleCat
