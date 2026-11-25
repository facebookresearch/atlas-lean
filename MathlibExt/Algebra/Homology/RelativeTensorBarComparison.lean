/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.MonoidalBar
public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Tensor descriptions of relative bar complexes

Let k be a commutative ring, R a possibly noncommutative k-algebra, M a right R-module and N a
left R-module, in a common module-category universe. Restriction of scalars makes R, M and N
into k-modules. The multiplication of R is an internal monoid, and the coefficient actions give
its internal modules. The resulting relative bar simplicial k-module has degree-d term M ⊗_k
R^{⊗d} ⊗_k N, with the M-action at the first face and the N-action at the last face.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

universe u

namespace ModuleCat.RelativeTensorBar

variable (k R : Type u) [CommRing k] [Ring R] [Algebra k R]

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
right R-module M, represented as a left Rᵐᵒᵖ-module, rightUnderlying is M restricted to k along
k → Rᵐᵒᵖ. The ground action is c·m = (op(algebraMap(c)))·m. -/
abbrev rightUnderlying (M : ModuleCat.{u} Rᵐᵒᵖ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj M

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
left R-module N, leftUnderlying is the k-module obtained by restriction of scalars along
algebraMap : k → R. Its scalar action is c·n = algebraMap(c)·n. -/
abbrev leftUnderlying (N : ModuleCat.{u} R) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k R)).obj N

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. The
object ringUnderlying in ModuleCat k is the additive group of R with its given k-module
structure. -/
abbrev ringUnderlying : ModuleCat.{u} k := ModuleCat.of k R

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. The
k-module R is an internal monoid in ModuleCat k, with multiplication R ⊗_k R → R sending r⊗s to
rs and unit k → R equal to the algebra map. This is the monoid structure ringMonObj. -/
@[instance_reducible]
def ringMonObj : MonObj (ringUnderlying k R) :=
  ModuleCat.MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of k R)

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
right R-module M, rightAction is the k-linear map M ⊗_k R → M sending m⊗r to m·r, where m·r
denotes the Rᵐᵒᵖ action (op r)·m. -/
def rightAction (M : ModuleCat.{u} Rᵐᵒᵖ) :
    rightUnderlying k R M ⊗ ringUnderlying k R ⟶ rightUnderlying k R M :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun m r => (op r : Rᵐᵒᵖ) • m)
    (by intro m m' r; exact smul_add (op r : Rᵐᵒᵖ) m m')
    (by
      intro c m r
      change (op r : Rᵐᵒᵖ) • ((op (algebraMap k R c) : Rᵐᵒᵖ) • m) =
        (op (algebraMap k R c) : Rᵐᵒᵖ) • ((op r : Rᵐᵒᵖ) • m)
      rw [← mul_smul, ← mul_smul]
      apply congrArg (fun s : Rᵐᵒᵖ => s • m)
      simpa only [op_mul] using congrArg (op : R → Rᵐᵒᵖ) (Algebra.commutes c r))
    (by intro m r s; exact add_smul (op r : Rᵐᵒᵖ) (op s : Rᵐᵒᵖ) m)
    (by
      intro c m r
      rw [Algebra.smul_def]
      change (op (algebraMap k R c * r) : Rᵐᵒᵖ) • m =
        (op (algebraMap k R c) : Rᵐᵒᵖ) • ((op r : Rᵐᵒᵖ) • m)
      rw [op_mul, ← mul_smul]
      apply congrArg (fun s : Rᵐᵒᵖ => s • m)
      simpa only [op_mul] using congrArg (op : R → Rᵐᵒᵖ) (Algebra.commutes c r))

@[simp]
theorem rightAction_tmul (M : ModuleCat.{u} Rᵐᵒᵖ) (m : M) (r : R) :
    (rightAction k R M).hom (m ⊗ₜ[k] r) = (op r : Rᵐᵒᵖ) • m := rfl

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
left R-module N, leftAction is the k-linear map R ⊗_k N → N sending r⊗n to r·n. -/
def leftAction (N : ModuleCat.{u} R) :
    ringUnderlying k R ⊗ leftUnderlying k R N ⟶ leftUnderlying k R N :=
  ModuleCat.MonoidalCategory.tensorLift (fun r n => r • n)
    (by intro r s n; exact add_smul r s n)
    (by
      intro c r n
      change (c • r) • n = (algebraMap k R c) • (r • n)
      rw [Algebra.smul_def, mul_smul])
    (by intro r m n; exact smul_add r m n)
    (by
      intro c r n
      change r • ((algebraMap k R c) • n) = (algebraMap k R c) • (r • n)
      rw [← mul_smul, ← mul_smul]
      exact congrArg (fun s : R => s • n) (Algebra.commutes c r).symm)

@[simp]
theorem leftAction_tmul (N : ModuleCat.{u} R) (r : R) (n : N) :
    (leftAction k R N).hom (r ⊗ₜ[k] n) = r • n := rfl

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. A
left R-module N becomes an internal left module over ringMonObj in ModuleCat k, with action R
⊗_k N → N, r⊗n ↦ r·n. Its unit and associativity laws are 1·n=n and (rs)·n=r·(s·n). -/
@[instance_reducible]
def leftModObj (N : ModuleCat.{u} R) :
    letI : MonObj (ringUnderlying k R) := ringMonObj k R
    ModObj (ringUnderlying k R) (leftUnderlying k R N) := by
  letI : MonObj (ringUnderlying k R) := ringMonObj k R
  exact
    { smul := leftAction k R N
      one_smul := by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro c n
        change (algebraMap k R c) • n = (algebraMap k R c) • n
        rfl
      mul_smul := by
        apply ModuleCat.MonoidalCategory.tensor_ext₃'
        intro r s n
        change (r * s) • n = r • (s • n)
        exact mul_smul r s n }

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. Let M
be a right R-module and μ_M : M ⊗_k R → M its action. The map M ⊗_k k → M obtained by tensoring
the unit k → R and then applying μ_M equals the right unitor of the k-module M; on elements this
is m·1=m. -/
theorem rightAction_one (M : ModuleCat.{u} Rᵐᵒᵖ) :
    letI : MonObj (ringUnderlying k R) := ringMonObj k R
    (rightUnderlying k R M ◁ MonObj.one) ≫ rightAction k R M =
      (ρ_ (rightUnderlying k R M)).hom := by
  let : MonObj (ringUnderlying k R) := ringMonObj k R
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m c
  change (op (algebraMap k R c) : Rᵐᵒᵖ) • m =
    (op (algebraMap k R c) : Rᵐᵒᵖ) • m
  rfl

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. Let M
be a right R-module. After identifying (M ⊗_k R) ⊗_k R with M ⊗_k (R ⊗_k R), the composite
applying multiplication in R and then the right action equals the composite applying the right
action twice. The element identity is m·(rs) = (m·r)·s, preserving the order r,s. -/
theorem rightAction_assoc (M : ModuleCat.{u} Rᵐᵒᵖ) :
    letI : MonObj (ringUnderlying k R) := ringMonObj k R
    (α_ (rightUnderlying k R M) (ringUnderlying k R) (ringUnderlying k R)).hom ≫
        (rightUnderlying k R M ◁ MonObj.mul) ≫ rightAction k R M =
      (rightAction k R M ▷ ringUnderlying k R) ≫ rightAction k R M := by
  let : MonObj (ringUnderlying k R) := ringMonObj k R
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro m r s
  change (op (r * s) : Rᵐᵒᵖ) • m = (op s : Rᵐᵒᵖ) • ((op r : Rᵐᵒᵖ) • m)
  rw [op_mul, mul_smul]

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
right R-module M, the functor M ⊗_k − is a right module over the tensor monad T = R ⊗_k −. Its
action M ⊗_k (R ⊗_k X) → M ⊗_k X is induced by the right action of R on M and satisfies the
monadic unit and multiplication laws. -/
def rightModule (M : ModuleCat.{u} Rᵐᵒᵖ) :
    letI : MonObj (ringUnderlying k R) := ringMonObj k R
    Monad.RightModule (Monad.tensorMonad (ringUnderlying k R)) (ModuleCat.{u} k) := by
  letI : MonObj (ringUnderlying k R) := ringMonObj k R
  exact Monad.rightModuleOfRightAction (rightUnderlying k R M) (ringUnderlying k R)
    (rightAction k R M) (rightAction_one k R M) (rightAction_assoc k R M)

/-- Let k be a commutative ring and R a k-algebra whose underlying ring may be noncommutative. For a
right R-module M and a left R-module N, literalBar is the simplicial k-module obtained from the
right tensor-monad module of M and the left action on N. Its degree-d term is M ⊗_k T^d(N), for
T=R ⊗_k −; the first face uses the M-action and the last face the N-action. -/
abbrev literalBar (M : ModuleCat.{u} Rᵐᵒᵖ) (N : ModuleCat.{u} R) :
    SimplicialObject (ModuleCat.{u} k) :=
  letI : MonObj (ringUnderlying k R) := ringMonObj k R
  letI : ModObj (ringUnderlying k R) (leftUnderlying k R N) := leftModObj k R N
  Monad.monoidalBar (rightUnderlying k R M) (ringUnderlying k R) (leftUnderlying k R N)
    (rightAction k R M) (rightAction_one k R M) (rightAction_assoc k R M) ⋙
      (evaluation (Discrete PUnit.{1}) (ModuleCat.{u} k)).obj (Discrete.mk PUnit.unit)

end ModuleCat.RelativeTensorBar
