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
# Right Lie modules and negative left actions

Let `R` be a commutative ring and `L` an `R`-Lie algebra. A right Lie module has a bilinear
action satisfying `m · [x,y] = (m · x) · y - (m · y) · x`. Negation gives a left Lie action
`[x,m] = -(m · x)`, and a left Lie action gives the right action `m · x = -[x,m]`.

A coefficient map over a Lie homomorphism `f : L → L'` is an `R`-linear map `g : M → N` with
`g(m · x) = g(m) · f(x)`. Such maps form a linear submodule and compose over composite Lie
maps. Over a fixed `L` and coefficient universe they give a preadditive `R`-linear category;
negation of the action defines an additive `R`-linear functor to left Lie modules. The scalar,
Lie-algebra, and coefficient universes are independent.
-/

@[expose] public section

open CategoryTheory
attribute [local instance] LieRing.ofAssociativeRing

universe w w' w'' v v' v'' u

/-- The bundled category of right Lie modules.

For an `R`-Lie algebra `L`, an object is an `R`-module `M` with a bilinear right action
satisfying `m · [x,y] = (m · x) · y - (m · y) · x`. -/
structure RightLieModuleCat (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L] where
  /-- The coefficient carrier of a right Lie module.

This type carries the additive group, scalar action, and bilinear right Lie action in its
specified universe. -/
  carrier : Type w
/-- The additive group of right Lie coefficients.

The coefficient carrier is an additive commutative group. -/
  [addCommGroup : AddCommGroup carrier]
/-- The scalar module of right Lie coefficients.

The coefficient carrier is a module over the commutative ground ring `R`. -/
  [moduleStructure : Module R carrier]
  /-- The endomorphism-valued right Lie action.

The `R`-linear map `L → End_R(M)` sends `x` to the endomorphism `m ↦ m · x`, encoding
bilinearity in both variables. -/
  action : L →ₗ[R] Module.End R carrier
  /-- The right Lie commutator identity.

For `x, y ∈ L` and `m ∈ M`, the action satisfies `m · [x,y] = (m · x) · y - (m · y) · x`, with
the indicated order of successive actions. -/
  right_lie : ∀ (x y : L) (m : carrier),
    action ⁅x, y⁆ m = action y (action x m) - action x (action y m)

attribute [instance] RightLieModuleCat.addCommGroup RightLieModuleCat.moduleStructure

namespace RightLieModuleCat

variable {R : Type u} [CommRing R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]
variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

/-- The carrier coercion for right Lie modules.

A bundled right Lie module is regarded as its coefficient carrier type. -/
instance instCoeSort : CoeSort (RightLieModuleCat.{w} R L) (Type w) := ⟨carrier⟩

/-- The right Lie module of a bilinear action.

An `R`-module `M` with `a : L →ₗ[R] End_R(M)` satisfying `a([x,y])(m) = a(y)(a(x)(m)) -
a(x)(a(y)(m))` defines a bundled right Lie module. -/
def of (M : Type w) [AddCommGroup M] [Module R M]
    (a : L →ₗ[R] Module.End R M)
    (ha : ∀ (x y : L) (m : M), a ⁅x, y⁆ m = a y (a x m) - a x (a y m)) :
    RightLieModuleCat.{w} R L where
  carrier := M
  action := a
  right_lie := ha

/-- Evaluation of a right Lie action.

For `m ∈ M` and `x ∈ L`, this denotes `m · x = M.action(x)(m)`. -/
def act (M : RightLieModuleCat.{w} R L) (m : M) (x : L) : M := M.action x m

/-- The bracket formula in right-action notation.

For a right Lie module, `m · [x,y] = (m · x) · y - (m · y) · x`. -/
@[simp]
theorem act_lie (M : RightLieModuleCat.{w} R L) (m : M) (x y : L) :
    act M m ⁅x, y⁆ = act M (act M m x) y - act M (act M m y) x :=
  M.right_lie x y m

/-- The left Lie-ring action obtained by negating a right action.

For a right Lie module `M`, the bracket `[x,m] = -(m · x)` gives a left Lie-ring-module
structure on the same coefficient carrier. -/
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

/-- The left Lie module associated to right coefficients.

Negating the right action defines the left action `[x,m] = -(m · x)`, retaining the
coefficient carrier and its `R`-module structure. -/
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

/-- The carrier of the left module associated to right coefficients.

Passing from a right Lie module to its negative left action retains the coefficient carrier. -/
@[simp]
theorem toLeft_carrier (M : RightLieModuleCat.{w} R L) :
    (toLeft M).carrier = M.carrier := rfl

/-- The sign formula for right-to-left Lie conversion.

The associated left action satisfies `[x,m] = -M.action(x)(m)`. -/
@[simp]
theorem toLeft_lie (M : RightLieModuleCat.{w} R L) (x : L) (m : M) :
    @Bracket.bracket L (toLeft M) inferInstance x m = -(M.action x m) := rfl

/-- The right Lie module associated to a left representation.

For a left Lie module `M`, define the right action by `m · x = -[x,m]` on the same scalar-
module carrier. -/
def fromLeft (M : LieModuleCat.{w} R L) : RightLieModuleCat.{w} R L where
  carrier := M
  action := -(LieModule.toEnd R L M).toLinearMap
  right_lie x y m := by
    change -⁅⁅x, y⁆, m⁆ = -⁅y, -⁅x, m⁆⁆ - (-⁅x, -⁅y, m⁆⁆)
    rw [lie_neg, lie_neg, neg_neg, neg_neg, leibniz_lie]
    abel
    rw [neg_one_smul, ← lie_skew y x, neg_lie]

/-- The sign formula for left-to-right Lie conversion.

The right action associated to a left Lie module sends `(m,x)` to `-[x,m]`. -/
@[simp]
theorem fromLeft_action (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    (fromLeft M).action x m = -⁅x, m⁆ := rfl

/-- The submodule of right coefficient maps over a Lie map.

For `f : L → L'`, this consists of `R`-linear maps `g : M → N` satisfying `g(m · x) = g(m) ·
f(x)`. The Lie-algebra and coefficient carrier universes may differ. -/
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

/-- Right Lie coefficient homomorphisms over a specified Lie map.

For `f : L → L'`, this is the type of `R`-linear maps between the coefficient modules which
intertwine the source action with the target action along `f`. -/
abbrev HomOver (f : L →ₗ⁅R⁆ L')
    (M : RightLieModuleCat.{w} R L) (N : RightLieModuleCat.{w'} R L') :=
  ↥(homOverSubmodule f M N)

namespace HomOver

/-- The linear map underlying a right coefficient homomorphism.

A coefficient homomorphism over `f : L → L'` has an underlying `R`-linear map between its
coefficient carriers. -/
abbrev toLinearMap {f : L →ₗ⁅R⁆ L'} {M : RightLieModuleCat.{w} R L}
    {N : RightLieModuleCat.{w'} R L'} (g : HomOver f M N) : M →ₗ[R] N := g.val

/-- The action equation for a right coefficient homomorphism.

For a map `g` over `f : L → L'`, one has `g(m · x) = g(m) · f(x)` for all source Lie and
coefficient elements. -/
theorem map_action {f : L →ₗ⁅R⁆ L'} {M : RightLieModuleCat.{w} R L}
    {N : RightLieModuleCat.{w'} R L'} (g : HomOver f M N) (x : L) (m : M) :
    g.toLinearMap (M.action x m) = N.action (f x) (g.toLinearMap m) := g.property x m

/-- Composition of right coefficient maps over Lie maps.

For `g : M → N` over `f : L → L'` and `k : N → P` over `h : L' → L''`, the composite
coefficient map `k ∘ g` intertwines the action along `h ∘ f`. -/
def comp {f : L →ₗ⁅R⁆ L'} {h : L' →ₗ⁅R⁆ L''}
    {M : RightLieModuleCat.{w} R L} {N : RightLieModuleCat.{w'} R L'}
    {P : RightLieModuleCat.{w''} R L''} (k : HomOver h N P) (g : HomOver f M N) :
    HomOver (h.comp f) M P :=
  ⟨k.toLinearMap.comp g.toLinearMap, by
    intro x m
    change k.toLinearMap (g.toLinearMap (M.action x m)) =
      P.action (h (f x)) (k.toLinearMap (g.toLinearMap m))
    rw [g.map_action x m, k.map_action (f x) (g.toLinearMap m)]⟩

/-- The value of a composite right coefficient map.

The composite of `g` and `k` sends `m` to `k(g(m))`. -/
@[simp]
theorem comp_apply {f : L →ₗ⁅R⁆ L'} {h : L' →ₗ⁅R⁆ L''}
    {M : RightLieModuleCat.{w} R L} {N : RightLieModuleCat.{w'} R L'}
    {P : RightLieModuleCat.{w''} R L''} (k : HomOver h N P) (g : HomOver f M N) (m : M) :
    (comp k g).toLinearMap m = k.toLinearMap (g.toLinearMap m) := rfl

end HomOver

/-- The category structure on right Lie modules.

For a fixed Lie algebra and coefficient universe, morphisms are coefficient maps over the
identity Lie map, with identity linear maps and ordinary composition. -/
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

/-- Extensionality of right Lie-module morphisms.

Two categorical right coefficient maps are equal if their underlying linear maps agree at
every coefficient element. -/
@[ext]
theorem hom_ext {M N : RightLieModuleCat.{w} R L} {f g : M ⟶ N}
    (h : ∀ m : M, f.toLinearMap m = g.toLinearMap m) : f = g := by
  apply Subtype.ext
  exact LinearMap.ext h

/-- The preadditive structure on right Lie modules.

Right coefficient morphisms form additive commutative groups under pointwise addition, and
composition is additive in both variables. -/
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

/-- The scalar module of right Lie morphisms.

For two right Lie modules over `L`, their morphism space is an `R`-module under pointwise
scalar multiplication. -/
instance homModule (M N : RightLieModuleCat.{w} R L) : Module R (M ⟶ N) :=
  inferInstanceAs (Module R (HomOver (LieHom.id : L →ₗ⁅R⁆ L) M N))

/-- The linear category of right Lie modules.

The `R`-module structures on right coefficient morphisms make composition linear in both
variables. -/
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

/-- The left Lie map associated to a right coefficient morphism.

A right coefficient map also intertwines the negative left actions, giving a left Lie-module
homomorphism with the same underlying linear map. -/
def toLeftMap {M N : RightLieModuleCat.{w} R L} (g : M ⟶ N) :
    toLeft M →ₗ⁅R,L⁆ toLeft N where
  toLinearMap := g.toLinearMap
  map_lie' := by
    intro x m
    change g.toLinearMap (-(M.action x m)) = -(N.action x (g.toLinearMap m))
    rw [g.toLinearMap.map_neg]
    exact congrArg Neg.neg (g.map_action x m)

/-- The value of a converted right coefficient morphism.

The associated left Lie-module map has the same coefficient value as the underlying right
coefficient linear map. -/
theorem toLeftMap_apply {M N : RightLieModuleCat.{w} R L} (g : M ⟶ N) (m : M) :
    toLeftMap g m = g.toLinearMap m := rfl

/-- The right-to-left Lie-module functor.

This functor negates each right Lie action to obtain a left action and retains the underlying
coefficient maps. -/
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

/-- Additivity of right-to-left Lie conversion.

The conversion functor preserves addition of coefficient morphisms. -/
instance toLeftFunctor_additive : (toLeftFunctor (R := R) (L := L)).Additive where
  map_add {M N} g h := by
    apply LieModuleHom.ext
    intro m
    rfl

/-- Scalar linearity of right-to-left Lie conversion.

For `r ∈ R`, the conversion functor sends `r • g` to `r` times the converted coefficient map. -/
instance toLeftFunctor_linear : (toLeftFunctor (R := R) (L := L)).Linear R where
  map_smul {M N} g r := by
    apply LieModuleHom.ext
    intro m
    rfl

/-- The trivial right Lie action on a scalar module.

For an `R`-module `M`, the zero action of `L` makes `M` a right Lie module. -/
def trivial (M : Type w) [AddCommGroup M] [Module R M] : RightLieModuleCat.{w} R L where
  carrier := M
  action := 0
  right_lie x y m := by simp

/-- The value of the trivial right Lie action.

In the trivial right module, the action of every `x ∈ L` on every `m ∈ M` is zero. -/
@[simp]
theorem trivial_action (M : Type w) [AddCommGroup M] [Module R M] (x : L) (m : M) :
    (trivial (R := R) (L := L) M).action x m = 0 := rfl

end RightLieModuleCat
