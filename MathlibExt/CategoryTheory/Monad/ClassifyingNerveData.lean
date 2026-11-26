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

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Prod
public import MathlibExt.CategoryTheory.NerveSingleObj
public import MathlibExt.CategoryTheory.Monad.MonoidalBar
public import MathlibExt.AlgebraicTopology.SimplicialObject.FromData
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataEvaluation
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso

/-!
# Classifying-bar coordinates and the opposite-monoid nerve

For a monoid G, the cartesian tensor monad is T(X) = G × X. Its powers at the point have
coordinates Gⁿ, ordered with the outermost factor first. The evaluated classifying bar has the
same coordinates: d₀ removes the first entry, dₙ₊₁ removes the last, dₖ₊₁ multiplies adjacent
entries gₖgₖ₊₁, and sᵢ inserts 1 at position i.

These maps agree with the nerve of the one-object category of Gᵐᵒᵖ. The opposite monoid makes
categorical composition f ≫ g = g*f agree with multiplication in the displayed tuple order.
The tuple comparisons give an isomorphism of simplicial face and degeneracy data for every
monoid G.

Mathematical source: J. P. May, The Geometry of Iterated Loop Spaces, Lecture Notes in
Mathematics 271, Springer, 1972, Chapter 9, Construction 9.6 and Remark 9.12,
https://doi.org/10.1007/BFb0067491.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe u

variable (G : Type u) [Monoid G]

open MonoidalCategory

/-- The cartesian monoid object associated to a monoid.

For a monoid G, its internal monoid structure in the cartesian category of types has the usual
unit and multiplication. -/
@[instance_reducible]
noncomputable def typeMonObj : MonObj (C := Type u) G :=
  (MonTypeEquivalenceMon.inverse.obj (MonCat.of G)).mon

attribute [local instance] typeMonObj

/-- The trivial left action on the point.

The one-point type PUnit is a left module over the cartesian monoid object G, with its unique
action map. -/
@[instance_reducible]
noncomputable def pointModObj : ModObj (M := G) (X := (PUnit : Type u)) :=
  ModObj.trivialAction G PUnit

attribute [local instance] pointModObj

/-- The trivial right action on the point.

The right action PUnit × G → PUnit is the unique map to the point. -/
def ractPt : PUnit ⊗ G ⟶ (PUnit : Type u) := ↾(fun _ => PUnit.unit)

/-- The right unit law of the point action.

Acting on the point by the monoid unit equals the cartesian right unitor. -/
theorem ractPt_one :
    (PUnit ◁ MonObj.one (X := G)) ≫ ractPt G = (ρ_ (PUnit : Type u)).hom := by
  ext x

/-- The associativity law of the point right action.

The two maps from (PUnit × G) × G to PUnit, obtained by multiplying in G or acting twice,
agree after the cartesian associator. -/
theorem ractPt_assoc :
    (α_ PUnit G G).hom ≫ (PUnit ◁ MonObj.mul (X := G)) ≫ ractPt G =
      (ractPt G ▷ G) ≫ ractPt G := by
  ext x

open Opposite

/-- Tuple coordinates for an iterated cartesian tensor monad.

For T(X) = G × X and n ≥ 0, this equivalence identifies Tⁿ(X) with (Fin n → G) × X. Coordinate
0 is the outermost G-factor, and the second component is the terminal X-coordinate. -/
noncomputable def powTupleGen (X : Type u) : (n : ℕ) →
    ((monadPow (tensorMonad G) n).obj X) ≃ (Fin n → G) × X
  | 0 =>
    (Equiv.cast (by rfl)).trans
      ((Equiv.punitProd X).symm.trans
        ((Equiv.ofUnique (PUnit.{u+1} : Type u) (Fin 0 → G)).prodCongr
          (Equiv.refl X)))
  | n + 1 =>
    (powTupleGen ((tensorMonad G).obj X) n).trans
      (((Equiv.refl (Fin n → G)).prodCongr (Equiv.cast (by rfl))).trans
        (((Equiv.prodAssoc (Fin n → G) G X).symm.trans
          ((Equiv.prodComm (Fin n → G) G).prodCongr (Equiv.refl X))).trans
          ((Fin.snocEquiv (fun _ : Fin (n + 1) => G)).prodCongr
            (Equiv.refl X))))

/-- Tuple coordinates for iterated powers at the point.

The equivalence Tⁿ(PUnit) ≃ (Fin n → G) removes the final point coordinate from the
generalized power equivalence. The outermost G-factor is coordinate 0. -/
noncomputable def powTupleEquiv (n : ℕ) :
    ((monadPow (tensorMonad G) n).obj PUnit) ≃ (Fin n → G) :=
  (powTupleGen G (PUnit.{u+1} : Type u) n).trans
    (Equiv.prodPUnit (Fin n → G))

/-- The tuple component at the successor power.

Reading Tⁿ⁺¹(X) first as Tⁿ(TX), the tuple at level n+1 is obtained by appending the
G-coordinate of the residual pair in TX to the level-n tuple. -/
theorem powTupleGen_succ_fst (X : Type u) (n : ℕ)
    (y : ((monadPow (tensorMonad G) (n + 1)).obj X)) :
    ((powTupleGen G X (n + 1)) y).1 =
      Fin.snoc
        (((powTupleGen G ((tensorMonad G).obj X) n) y).1)
        ((Equiv.cast (by rfl : ((tensorMonad G).obj X) = (G × X))
          ((powTupleGen G ((tensorMonad G).obj X) n) y).2).1) := by
  simp only [powTupleGen, Equiv.trans_apply, Equiv.prodCongr_apply]
  rfl

/-- The base component at the successor power.

The X-coordinate of the generalized tuple equivalence at level n+1 is the X-component of the
residual pair in TX obtained from the level-n equivalence. -/
theorem powTupleGen_succ_snd (X : Type u) (n : ℕ)
    (y : ((monadPow (tensorMonad G) (n + 1)).obj X)) :
    ((powTupleGen G X (n + 1)) y).2 =
      ((Equiv.cast (by rfl : ((tensorMonad G).obj X) = (G × X))
        ((powTupleGen G ((tensorMonad G).obj X) n) y).2).2) := by
  simp only [powTupleGen, Equiv.trans_apply, Equiv.prodCongr_apply]
  rfl

/-- The product description of the right point-module fiber.

For a type Y, the right-module functor associated to the point action has value PUnit × Y.
This map identifies that product with the functor value. -/
noncomputable def rCastIn (Y : Type u) (w : PUnit × Y) :
    (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
      (ractPt_assoc G)).functor.obj Y :=
  Equiv.cast (by rfl : (PUnit × Y) = ((rightModuleOfRightAction PUnit G
    (ractPt G) (ractPt_one G) (ractPt_assoc G)).functor.obj Y)) w

/-- The product projection of the right point-module fiber.

This map identifies the right point-module functor value at Y with PUnit × Y, in the reverse
direction of rCastIn. -/
noncomputable def rCastOut (Y : Type u) (w :
    (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
      (ractPt_assoc G)).functor.obj Y) : PUnit × Y :=
  Equiv.cast (by rfl : ((rightModuleOfRightAction PUnit G (ractPt G)
    (ractPt_one G) (ractPt_assoc G)).functor.obj Y) = (PUnit × Y)) w

/-- The base component at power zero.

For T⁰(X) = X, the generalized tuple equivalence has the empty G-tuple and retains its
argument as the X-component. -/
theorem powTupleGen_zero_snd (X : Type u)
    (z : ((monadPow (tensorMonad G) 0).obj X)) :
    ((powTupleGen G X 0) z).2 = Equiv.cast (by rfl) z := by
  simp only [powTupleGen, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.cast_apply]
  rfl

/-- Iterated right action preserves the generalized base point.

By induction on `n` generalizing `X`: the zero case holds by `rfl`
(the action drops the head and keeps the tail pair); the successor case
peels one `powTupleGen_succ_snd` layer on each side and applies the
induction hypothesis at `T.obj X`, since `RAP_{n+1}^X = RAP_n^{T.obj X}`
definitionally. -/
private theorem genZeroSnd : ∀ (n : ℕ) (X : Type u)
    (y : PUnit × ((monadPow (tensorMonad G) (n + 1)).obj X)),
    (let aR := (ConcreteCategory.hom (rightActionPow (tensorMonad G)
      (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
        (ractPt_assoc G)) n X))
      ((rCastIn G ((monadPow (tensorMonad G) (n + 1)).obj X)) y);
      let aP := (rCastOut G ((monadPow (tensorMonad G) n).obj X)) aR;
      (((powTupleGen G X n) aP.2).2)) =
      (((powTupleGen G X (n + 1)) y.2)).2 := by
  intro n X y
  induction n generalizing X with
  | zero =>
    obtain ⟨p, z⟩ := y
    have hRAP0 : rightActionPow (tensorMonad G)
        (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
          (ractPt_assoc G)) 0 X =
        (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
          (ractPt_assoc G)).action.app X := rfl
    rw [hRAP0, powTupleGen_succ_snd, powTupleGen_zero_snd,
      powTupleGen_zero_snd]
    rfl
  | succ n ih =>
    obtain ⟨p, z⟩ := y
    have hRAP : rightActionPow (tensorMonad G)
        (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
          (ractPt_assoc G)) (n + 1) X =
        rightActionPow (tensorMonad G)
          (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
            (ractPt_assoc G)) n ((tensorMonad G).obj X) := rfl
    rw [hRAP, powTupleGen_succ_snd, powTupleGen_succ_snd]
    have ihS := ih ((tensorMonad G).obj X) (p, z)
    exact congrArg _root_.Prod.snd ihS

/-- Tuple coordinates of the right point action.

The degree-n iterated right action on PUnit × Tⁿ⁺¹(X) removes the outermost G-coordinate.
Under the generalized tuple equivalence, its tuple component is the tail of the original
tuple. -/
theorem genZeroFst : ∀ (n : ℕ) (X : Type u)
    (y : PUnit × ((monadPow (tensorMonad G) (n + 1)).obj X)),
    (let aR := (ConcreteCategory.hom (rightActionPow (tensorMonad G)
      (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
        (ractPt_assoc G)) n X))
      ((rCastIn G ((monadPow (tensorMonad G) (n + 1)).obj X)) y);
      let aP := (rCastOut G ((monadPow (tensorMonad G) n).obj X)) aR;
      (((powTupleGen G X n) aP.2).1)) =
      Fin.tail ((((powTupleGen G X (n + 1)) y.2)).1) := by
  have hTS : ∀ {m : ℕ} (t : Fin (m + 1) → G) (g : G),
      Fin.tail (Fin.snoc (α := fun _ => G) t g) =
        Fin.snoc (α := fun _ => G) (Fin.tail t) g := by
    intro m t g
    funext j
    cases j using Fin.lastCases with
    | last =>
      have hL : (Fin.last m).succ = Fin.last (m + 1) := rfl
      simp only [Fin.tail]
      rw [hL, Fin.snoc_last, Fin.snoc_last]
    | cast j =>
      simp only [Fin.tail]
      have h : (Fin.castSucc j).succ = Fin.castSucc j.succ := by
        exact (Fin.castSucc_succ j).symm
      rw [h, Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl
  intro n X y
  induction n generalizing X with
  | zero =>
    exact Subsingleton.elim _ _
  | succ n ih =>
    obtain ⟨p, z⟩ := y
    have hRAP : rightActionPow (tensorMonad G)
        (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
          (ractPt_assoc G)) (n + 1) X =
        rightActionPow (tensorMonad G)
          (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
            (ractPt_assoc G)) n ((tensorMonad G).obj X) := rfl
    rw [hRAP, powTupleGen_succ_fst, powTupleGen_succ_fst, hTS,
      Fin.snoc_inj]
    refine ⟨?_, ?_⟩
    · exact ih ((tensorMonad G).obj X) (p, z)
    · exact congrArg
        (fun w : ((tensorMonad G).obj X) =>
          ((Equiv.cast (by rfl : ((tensorMonad G).obj X) = (G × X))
            w).1))
        (genZeroSnd G n ((tensorMonad G).obj X) (p, z))

/-- The base coordinate under an iterated monad map.

For a map f : X → Y, the map Tⁿ(f) sends the base coordinate x of Tⁿ(X) to f(x) under the
generalized tuple equivalence. -/
theorem genMapSnd : ∀ (n : ℕ) (X Y : Type u) (f : X ⟶ Y)
    (y : ((monadPow (tensorMonad G) n).obj X)),
    (((powTupleGen G Y n) ((monadPow (tensorMonad G) n).map f y)).2) =
      f (((powTupleGen G X n) y).2) := by
  intro n X Y f y
  induction n generalizing X Y with
  | zero =>
    rw [powTupleGen_zero_snd, powTupleGen_zero_snd]
    rfl
  | succ n ih =>
    rw [powTupleGen_succ_snd, powTupleGen_succ_snd]
    have hM : ((monadPow (tensorMonad G) (n + 1)).map f y) =
        ((monadPow (tensorMonad G) n).map ((tensorMonad G).map f) y) := rfl
    have ihS := ih ((tensorMonad G).obj X) ((tensorMonad G).obj Y)
      ((tensorMonad G).map f) y
    rw [hM, ihS]
    rfl

/-- The group coordinates under an iterated monad map.

For f : X → Y, applying Tⁿ(f) preserves every G-coordinate of the generalized tuple
equivalence. -/
theorem genMapFst : ∀ (n : ℕ) (X Y : Type u) (f : X ⟶ Y)
    (y : ((monadPow (tensorMonad G) n).obj X)),
    (((powTupleGen G Y n) ((monadPow (tensorMonad G) n).map f y)).1) =
      (((powTupleGen G X n) y).1) := by
  intro n X Y f y
  induction n generalizing X Y with
  | zero =>
    exact Subsingleton.elim _ _
  | succ n ih =>
    rw [powTupleGen_succ_fst, powTupleGen_succ_fst, Fin.snoc_inj]
    have hM : ((monadPow (tensorMonad G) (n + 1)).map f y) =
        ((monadPow (tensorMonad G) n).map ((tensorMonad G).map f) y) := rfl
    refine ⟨?_, ?_⟩
    · rw [hM]
      exact ih ((tensorMonad G).obj X) ((tensorMonad G).obj Y)
        ((tensorMonad G).map f) y
    · rw [hM, genMapSnd G n ((tensorMonad G).obj X) ((tensorMonad G).obj Y)
        ((tensorMonad G).map f) y]
      rfl

/-- The tuple component of a map on the innermost pair.

For f : TX → Y, the map Tⁿ(f) on Tⁿ⁺¹(X) removes the last G-coordinate from its tuple
component. The retained tuple is Fin.init of the source tuple. -/
theorem genLastFst : ∀ (n : ℕ) (X Y : Type u)
    (f : (tensorMonad G).obj X ⟶ Y)
    (y : PUnit × ((monadPow (tensorMonad G) (n + 1)).obj X)),
    (((powTupleGen G Y n) ((monadPow (tensorMonad G) n).map f y.2)).1) =
      Fin.init ((((powTupleGen G X (n + 1)) y.2)).1) := by
  intro n X Y f y
  obtain ⟨p, z⟩ := y
  rw [powTupleGen_succ_fst, Fin.init_snoc]
  exact genMapFst G n _ _ f z

/-- Multiplication of adjacent tuple entries.

For t : Fin (n+1) → G and m : Fin n, contract coordinates m and m+1 by the ordered product
tₘtₘ₊₁, producing a tuple of length n. -/
def tupleMulAt (n : ℕ) (t : Fin (n + 1) → G) (m : Fin n) :
    Fin n → G :=
  Fin.contractNth m.castSucc (· * ·) t

/-- Collapsing below the head preserves the snoc structure.

This `Fin.snoc` commutation is not in pinned Mathlib, which supplies only the
pointwise `Fin.contractNth_apply_of_lt/of_eq/of_gt` lemmas used below. -/
private theorem tupleMulAt_snoc (n : ℕ) (u : Fin (n + 1) → G) (g : G)
    (m' : Fin n) :
    tupleMulAt G (n + 1) (Fin.snoc u g) m'.castSucc =
      Fin.snoc (tupleMulAt G n u m') g := by
  funext j
  cases j using Fin.lastCases with
  | last =>
    have hlt : ((m'.castSucc.castSucc : Fin (n + 2)) : ℕ) <
        ((Fin.last n : Fin (n + 1)) : ℕ) := by
      simp only [Fin.val_castSucc, Fin.val_last]
      have := m'.isLt
      omega
    have hL : tupleMulAt G (n + 1) (Fin.snoc u g) m'.castSucc (Fin.last n) =
        (Fin.snoc (α := fun _ => G) u g) (Fin.last n).succ := by
      simp only [tupleMulAt]
      exact Fin.contractNth_apply_of_gt _ _ _ _ hlt
    have e : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [hL, e, Fin.snoc_last, Fin.snoc_last]
  | cast j' =>
    by_cases h1 : j'.val < m'.val <;> by_cases h2 : j'.val = m'.val
    · exact absurd h2 (ne_of_lt h1)
    · have h1c : ((Fin.castSucc j' : Fin (n + 1)) : ℕ) <
          ((m'.castSucc.castSucc : Fin (n + 2)) : ℕ) := by
        simpa using h1
      have hL : tupleMulAt G (n + 1) (Fin.snoc u g) m'.castSucc
          (Fin.castSucc j') =
          (Fin.snoc (α := fun _ => G) u g) (Fin.castSucc (Fin.castSucc j')) := by
        simp only [tupleMulAt]
        exact Fin.contractNth_apply_of_lt _ _ _ _ h1c
      have hR : tupleMulAt G n u m' j' = u j'.castSucc := by
        simp only [tupleMulAt]
        exact Fin.contractNth_apply_of_lt _ _ _ _ h1
      rw [Fin.snoc_castSucc, hL, hR, Fin.snoc_castSucc]
    · have hj : m' = j' := (Fin.ext h2).symm
      subst hj
      have hE : ((Fin.castSucc m' : Fin (n + 1)) : ℕ) =
          ((m'.castSucc.castSucc : Fin (n + 2)) : ℕ) := rfl
      have hL : tupleMulAt G (n + 1) (Fin.snoc u g) m'.castSucc
          (Fin.castSucc m') =
          (Fin.snoc (α := fun _ => G) u g) (Fin.castSucc (Fin.castSucc m')) *
            (Fin.snoc (α := fun _ => G) u g) (Fin.castSucc m').succ := by
        simp only [tupleMulAt]
        exact Fin.contractNth_apply_of_eq _ _ _ _ hE
      have hR : tupleMulAt G n u m' m' = u m'.castSucc * u m'.succ := by
        simp only [tupleMulAt]
        exact Fin.contractNth_apply_of_eq _ _ _ _ rfl
      rw [Fin.snoc_castSucc, hL, hR, Fin.snoc_castSucc,
        ← Fin.castSucc_succ, Fin.snoc_castSucc]
    · have hgt1 : ((m'.castSucc.castSucc : Fin (n + 2)) : ℕ) <
          ((Fin.castSucc j' : Fin (n + 1)) : ℕ) := by
        simp only [Fin.val_castSucc]
        omega
      have hL : tupleMulAt G (n + 1) (Fin.snoc u g) m'.castSucc
          (Fin.castSucc j') =
          (Fin.snoc (α := fun _ => G) u g) (Fin.castSucc j').succ := by
        simp only [tupleMulAt]
        exact Fin.contractNth_apply_of_gt _ _ _ _ hgt1
      have hgt : (m'.val) < (j'.val) := by omega
      have hR : tupleMulAt G n u m' j' = u j'.succ := by
        simp only [tupleMulAt]
        exact Fin.contractNth_apply_of_gt _ _ _ _ hgt
      rw [Fin.snoc_castSucc, hL, hR,
        ← Fin.castSucc_succ, Fin.snoc_castSucc]

/-- Insertion of a unit into a tuple.

For t : Fin n → G and m : Fin (n+1), insert the identity 1 at position m to obtain a tuple of
length n+1. -/
def tupleInsAt (n : ℕ) (t : Fin n → G) (m : Fin (n + 1)) :
    Fin (n + 1) → G :=
  Fin.insertNth m (1 : G) t

/-- Inserting below the head preserves the snoc structure.

This `Fin.snoc` commutation is not in pinned Mathlib. The three local `have`s
below are the head-first `val` forms of pinned
`Fin.insertNth_apply_below/apply_same/apply_above` (via `Fin.lt_def`; the
constant-family casts vanish by `simp` and the `castPred`/`pred` arguments
agree by `Fin.ext`); no standalone duplication is retained. -/
private theorem tupleInsAt_snoc (n : ℕ) (u : Fin n → G) (g : G)
    (m' : Fin (n + 1)) :
    tupleInsAt G (n + 1) (Fin.snoc u g) m'.castSucc =
      Fin.snoc (tupleInsAt G n u m') g := by
  have hBelow : ∀ {k : ℕ} (t : Fin k → G) (m : Fin (k + 1)) (j : Fin (k + 1))
      (h : j.val < m.val),
      tupleInsAt G k t m j = t ⟨j.val, by have := m.isLt; omega⟩ := by
    intro k t m j h
    simp only [tupleInsAt]
    rw [Fin.insertNth_apply_below (Fin.lt_def.mpr h)]
    simp
    congr 1
  have hAt : ∀ {k : ℕ} (t : Fin k → G) (m : Fin (k + 1)),
      tupleInsAt G k t m m = 1 := by
    intro k t m
    simp only [tupleInsAt]
    rw [Fin.insertNth_apply_same]
  have hAbove : ∀ {k : ℕ} (t : Fin k → G) (m : Fin (k + 1)) (j : Fin (k + 1))
      (h1 : ¬ j.val < m.val) (h2 : j.val ≠ m.val),
      tupleInsAt G k t m j = t ⟨j.val - 1, by have := j.isLt; omega⟩ := by
    intro k t m j h1 h2
    have hlt : m < j := Fin.lt_def.mpr (by omega)
    simp only [tupleInsAt]
    rw [Fin.insertNth_apply_above hlt]
    simp
    congr 1
  funext j
  cases j using Fin.lastCases with
  | last =>
    have hm := m'.isLt
    have h1 : ¬ (Fin.last (n + 1)).val < ((m'.castSucc : Fin (n + 2))).val := by
      rw [Fin.val_last, Fin.val_castSucc]; omega
    have h2 : (Fin.last (n + 1)).val ≠ ((m'.castSucc : Fin (n + 2))).val := by
      rw [Fin.val_last, Fin.val_castSucc]; omega
    rw [hAbove _ _ _ h1 h2, Fin.snoc_last]
    have e : (⟨(Fin.last (n + 1)).val - 1, by omega⟩ : Fin (n + 1)) =
        Fin.last n := by
      apply Fin.ext
      simp [Fin.val_last]
    rw [e, Fin.snoc_last]
  | cast j' =>
    by_cases h1 : j'.val < m'.val <;> by_cases h2 : j'.val = m'.val
    · exact absurd h2 (ne_of_lt h1)
    · have h1' : (Fin.castSucc j').val < ((m'.castSucc : Fin (n + 2))).val := by
        simpa using h1
      rw [hBelow _ _ _ h1', Fin.snoc_castSucc,
        hBelow _ _ _ h1]
      have hlt : j'.val < n := by have := m'.isLt; omega
      simp only [Fin.snoc, Fin.val_castSucc, hlt, dite_true, Fin.castLT]
      rfl
    · have hj : j' = m' := Fin.ext h2
      subst hj
      rw [hAt, Fin.snoc_castSucc, hAt]
    · have h1' : ¬ (Fin.castSucc j').val < ((m'.castSucc : Fin (n + 2))).val := by
        simpa using h1
      have h2' : (Fin.castSucc j').val ≠ ((m'.castSucc : Fin (n + 2))).val := by
        simpa using h2
      rw [hAbove _ _ _ h1' h2', Fin.snoc_castSucc,
        hAbove _ _ _ h1 h2]
      have hlt : j'.val - 1 < n := by have := j'.isLt; have := m'.isLt; omega
      simp only [Fin.snoc, Fin.val_castSucc, hlt, dite_true, Fin.castLT]
      rfl

/-- The tensor-monad multiplication multiplies the head pair in `Type`.

`T.μ.app X` is `tensorLeftTensor.inv ≫ (mul ▷ X)`: the inverse exposes
`((g₁, g₂), x)` and the whiskered multiplication collapses the head pair to
`g₁ * g₂`. Everything here is `rfl`-transparent. -/
private theorem muApp_head (X : Type u)
    (c : ((tensorMonad G).obj ((tensorMonad G).obj X))) :
    ((Equiv.cast (by rfl : ((tensorMonad G).obj X) = (G × X))
      (ConcreteCategory.hom ((tensorMonad G).μ.app X) c)).1) =
    (((Equiv.cast (by rfl : ((tensorMonad G).obj ((tensorMonad G).obj X)) =
        (G × (G × X))) c).1) *
     ((Equiv.cast (by rfl : ((tensorMonad G).obj ((tensorMonad G).obj X)) =
        (G × (G × X))) c).2.1)) := by
  rfl

/-- The tensor-monad multiplication preserves the base point in `Type`. -/
private theorem muApp_base (X : Type u)
    (c : ((tensorMonad G).obj ((tensorMonad G).obj X))) :
    ((Equiv.cast (by rfl : ((tensorMonad G).obj X) = (G × X))
      (ConcreteCategory.hom ((tensorMonad G).μ.app X) c)).2) =
    ((Equiv.cast (by rfl : ((tensorMonad G).obj X) = (G × X))
      ((Equiv.cast (by rfl : ((tensorMonad G).obj ((tensorMonad G).obj X)) =
        (G × ((tensorMonad G).obj X))) c).2)).2) := by
  rfl

/-- The tensor-monad unit inserts `1` at the head in `Type`.

`T.η.app X` is `(λ_ X).inv ≫ (one ▷ X)`: the unitor inverse pairs the base
with `unit`, and the whiskered `one` replaces it by `1`. -/
private theorem etaApp_head (X : Type u) (x : X) :
    ((Equiv.cast (by rfl : ((tensorMonad G).obj X) = (G × X))
      (ConcreteCategory.hom ((tensorMonad G).η.app X) x)).1) = 1 := by
  rfl

/-- The tensor-monad unit preserves the base point in `Type`. -/
private theorem etaApp_base (X : Type u) (x : X) :
    ((Equiv.cast (by rfl : ((tensorMonad G).obj X) = (G × X))
      (ConcreteCategory.hom ((tensorMonad G).η.app X) x)).2) = x := by
  rfl

/-- `muAtPos` preserves the generalized base point.

By induction on `n`: the zero case is vacuous; the `⟨0⟩` case peels one
`powTupleGen_succ_snd` layer on each side and applies `genMapSnd` (the
tensor-monad multiplication preserves the base point); the `⟨jv+1⟩` case
peels one layer and applies the hypothesis at `T.obj X`. -/
private theorem genMuSnd : ∀ (n : ℕ) (X : Type u) (j : Fin n)
    (y : ((monadPow (tensorMonad G) (n + 1)).obj X)),
    (((powTupleGen G X n) ((tensorMonad G).muAtPos n j X y)).2) =
      (((powTupleGen G X (n + 1)) y).2) := by
  intro n
  induction n with
  | zero =>
    intro X j
    exact Fin.elim0 j
  | succ n ih =>
    intro X j y
    match j with
    | ⟨0, h0⟩ =>
      have hM : (tensorMonad G).muAtPos (n + 1) ⟨0, h0⟩ X y =
          ((monadPow (tensorMonad G) n).map ((tensorMonad G).μ.app X) y) := rfl
      rw [hM, powTupleGen_succ_snd,
        genMapSnd G n _ _ ((tensorMonad G).μ.app X) y,
        powTupleGen_succ_snd, powTupleGen_succ_snd, muApp_base]
      rfl
    | ⟨jv + 1, hj⟩ =>
      have hEq := muAtPos_succ_eq (T := tensorMonad G) (n := n)
        (k := (⟨jv, by omega⟩ : Fin n)) (X := X)
      have hM : (tensorMonad G).muAtPos (n + 1) ⟨jv + 1, hj⟩ X =
          (tensorMonad G).muAtPos n (⟨jv, by omega⟩ : Fin n)
            ((tensorMonad G).obj X) := hEq
      have hMy : (tensorMonad G).muAtPos (n + 1) ⟨jv + 1, hj⟩ X y =
          (tensorMonad G).muAtPos n (⟨jv, by omega⟩ : Fin n)
            ((tensorMonad G).obj X) y := by
        rw [hM]
      rw [hMy, powTupleGen_succ_snd, powTupleGen_succ_snd]
      exact congrArg _root_.Prod.snd
        (ih _ (⟨jv, by omega⟩ : Fin n) y)

/-- Tuple coordinates of an iterated multiplication.

For j : Fin n, the monad multiplication at position j contracts adjacent tuple coordinates at
m = n−1−j. This reversal relates the monad-position convention to the outermost-first tuple
order. -/
theorem genMuFst : ∀ (n : ℕ) (X : Type u) (j : Fin n)
    (y : ((monadPow (tensorMonad G) (n + 1)).obj X)),
    (((powTupleGen G X n) ((tensorMonad G).muAtPos n j X y)).1) =
      tupleMulAt G n (((powTupleGen G X (n + 1)) y).1)
        ⟨n - 1 - j.val, by have := j.isLt; omega⟩ := by
  intro n
  induction n with
  | zero =>
    intro X j
    exact Fin.elim0 j
  | succ n ih =>
    intro X j y
    match j with
    | ⟨0, h0⟩ =>
      have hM : (tensorMonad G).muAtPos (n + 1) ⟨0, h0⟩ X y =
          ((monadPow (tensorMonad G) n).map ((tensorMonad G).μ.app X) y) := rfl
      have hm :
          (⟨n + 1 - 1 - (⟨0, h0⟩ : Fin (n + 1)).val, by
            have h : (⟨0, h0⟩ : Fin (n + 1)).val = 0 := rfl; omega⟩ :
            Fin (n + 1)) =
          Fin.last n := by
        apply Fin.ext
        change n + 1 - 1 - 0 = (Fin.last n).val
        change n + 1 - 1 - 0 = n
        rfl
      rw [hM, hm]
      funext p
      cases p using Fin.lastCases with
      | last =>
        rw [powTupleGen_succ_fst, Fin.snoc_last]
        simp only [tupleMulAt]
        rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl,
          powTupleGen_succ_fst, Fin.snoc_castSucc, powTupleGen_succ_fst,
          Fin.snoc_last]
        have e : (Fin.last n).succ = Fin.last (n + 1) := rfl
        rw [e, Fin.snoc_last,
          genMapSnd G n _ _ ((tensorMonad G).μ.app X) y, muApp_head,
          powTupleGen_succ_snd]
        rfl
      | cast p' =>
        have hbelow : (Fin.castSucc p').val < (Fin.last n).val := by
          simp [Fin.val_last]
        rw [powTupleGen_succ_fst, Fin.snoc_castSucc,
          genMapFst G n _ _ ((tensorMonad G).μ.app X) y,
          powTupleGen_succ_fst]
        simp only [tupleMulAt]
        rw [Fin.contractNth_apply_of_lt _ _ _ _ hbelow, Fin.snoc_castSucc,
          powTupleGen_succ_fst, Fin.snoc_castSucc]
        rfl
    | ⟨jv + 1, hj⟩ =>
      have hEq := muAtPos_succ_eq (T := tensorMonad G) (n := n)
        (k := (⟨jv, by omega⟩ : Fin n)) (X := X)
      have hM : (tensorMonad G).muAtPos (n + 1) ⟨jv + 1, hj⟩ X y =
          (tensorMonad G).muAtPos n (⟨jv, by omega⟩ : Fin n)
            ((tensorMonad G).obj X) y := by
        rw [hEq]
      have hm :
          (⟨n + 1 - 1 - (⟨jv + 1, hj⟩ : Fin (n + 1)).val, by
            have h : (⟨jv + 1, hj⟩ : Fin (n + 1)).val = jv + 1 := rfl
            omega⟩ : Fin (n + 1)) =
          (⟨n - 1 - jv, by omega⟩ : Fin n).castSucc := by
        apply Fin.ext
        change n + 1 - 1 - (jv + 1) = ((⟨n - 1 - jv, by omega⟩ : Fin n).castSucc).val
        change n + 1 - 1 - (jv + 1) = n - 1 - jv
        omega
      rw [hM, hm, powTupleGen_succ_fst, powTupleGen_succ_fst, tupleMulAt_snoc,
        Fin.snoc_inj]
      refine ⟨?_, ?_⟩
      · exact ih _ (⟨jv, by omega⟩ : Fin n) y
      · rw [genMuSnd G n _ (⟨jv, by omega⟩ : Fin n) y]

/-- `etaAtPos` preserves the generalized base point.

By induction on `n`: the zero case is `etaApp_base`; the `⟨0⟩` case peels
one `powTupleGen_succ_snd` layer on each side and applies `genMapSnd` (the
tensor-monad unit preserves the base point); the `⟨jv+1⟩` case peels one
layer and applies the hypothesis at `T.obj X`. -/
private theorem genEtaSnd : ∀ (n : ℕ) (X : Type u) (j : Fin (n + 1))
    (y : ((monadPow (tensorMonad G) n).obj X)),
    (((powTupleGen G X (n + 1)) ((tensorMonad G).etaAtPos n j X y)).2) =
      (((powTupleGen G X n) y).2) := by
  intro n
  induction n with
  | zero =>
    intro X j y
    have hj : j = ⟨0, by omega⟩ := by ext; have := j.isLt; omega
    subst hj
    rfl
  | succ n ih =>
    intro X j y
    match j with
    | ⟨0, h0⟩ =>
      have hM : (tensorMonad G).etaAtPos (n + 1) ⟨0, h0⟩ X y =
          ((monadPow (tensorMonad G) (n + 1)).map ((tensorMonad G).η.app X)
            y) := rfl
      rw [hM, powTupleGen_succ_snd,
        genMapSnd G (n + 1) _ _ ((tensorMonad G).η.app X) y,
        powTupleGen_succ_snd, powTupleGen_succ_snd, etaApp_base]
      rfl
    | ⟨jv + 1, hj⟩ =>
      have hEq := etaAtPos_succ_eq (T := tensorMonad G) (n := n)
        (k := (⟨jv, by omega⟩ : Fin (n + 1))) (X := X)
      have hM : (tensorMonad G).etaAtPos (n + 1) ⟨jv + 1, hj⟩ X y =
          (tensorMonad G).etaAtPos n (⟨jv, by omega⟩ : Fin (n + 1))
            ((tensorMonad G).obj X) y := by
        rw [hEq]
      rw [hM, powTupleGen_succ_snd, powTupleGen_succ_snd]
      exact congrArg _root_.Prod.snd
        (ih _ (⟨jv, by omega⟩ : Fin (n + 1)) y)

/-- Tuple coordinates of an iterated unit insertion.

For j : Fin (n+1), insertion of the monad unit at position j inserts the monoid identity into
the tuple at m = n−j. -/
theorem genEtaFst : ∀ (n : ℕ) (X : Type u) (j : Fin (n + 1))
    (y : ((monadPow (tensorMonad G) n).obj X)),
    (((powTupleGen G X (n + 1)) ((tensorMonad G).etaAtPos n j X y)).1) =
      tupleInsAt G n (((powTupleGen G X n) y).1)
        ⟨n - j.val, by have := j.isLt; omega⟩ := by
  intro n
  induction n with
  | zero =>
    intro X j y
    have hj : j = ⟨0, by omega⟩ := by ext; have := j.isLt; omega
    subst hj
    have hm : (⟨0 - (⟨0, by omega⟩ : Fin 1).val, by omega⟩ : Fin 1) =
        (0 : Fin 1) := by ext; rfl
    rw [hm]
    funext p
    have hp : p = (0 : Fin 1) := by ext; have := p.isLt; omega
    subst hp
    rfl
  | succ n ih =>
    intro X j y
    match j with
    | ⟨0, h0⟩ =>
      have hM : (tensorMonad G).etaAtPos (n + 1) ⟨0, h0⟩ X y =
          ((monadPow (tensorMonad G) (n + 1)).map ((tensorMonad G).η.app X)
            y) := rfl
      have hm :
          (⟨n + 1 - (⟨0, h0⟩ : Fin (n + 2)).val, by
            have h : (⟨0, h0⟩ : Fin (n + 2)).val = 0 := rfl; omega⟩ :
            Fin (n + 2)) =
          Fin.last (n + 1) := by
        apply Fin.ext
        change n + 1 - 0 = (Fin.last (n + 1)).val
        change n + 1 - 0 = n + 1
        omega
      rw [hM, hm]
      funext p
      cases p using Fin.lastCases with
      | last =>
        rw [powTupleGen_succ_fst, Fin.snoc_last]
        simp only [tupleInsAt]
        rw [Fin.insertNth_apply_same,
          genMapSnd G (n + 1) _ _ ((tensorMonad G).η.app X) y, etaApp_head]
      | cast p' =>
        have hbelow : (Fin.castSucc p').val < (Fin.last (n + 1)).val := by
          simp [Fin.val_last]
        have hIns : ∀ (t : Fin (n + 1) → G) (m : Fin (n + 2)) (j : Fin (n + 2))
            (h : j.val < m.val),
            tupleInsAt G (n + 1) t m j =
              t ⟨j.val, by have := m.isLt; omega⟩ := by
          intro t m j h
          simp only [tupleInsAt]
          rw [Fin.insertNth_apply_below (Fin.lt_def.mpr h)]
          simp
          congr 1
        rw [powTupleGen_succ_fst, Fin.snoc_castSucc,
          genMapFst G (n + 1) _ _ ((tensorMonad G).η.app X) y,
          powTupleGen_succ_fst,
          hIns _ _ _ hbelow, powTupleGen_succ_fst]
        rfl
    | ⟨jv + 1, hj⟩ =>
      have hEq := etaAtPos_succ_eq (T := tensorMonad G) (n := n)
        (k := (⟨jv, by omega⟩ : Fin (n + 1))) (X := X)
      have hM : (tensorMonad G).etaAtPos (n + 1) ⟨jv + 1, hj⟩ X y =
          (tensorMonad G).etaAtPos n (⟨jv, by omega⟩ : Fin (n + 1))
            ((tensorMonad G).obj X) y := by
        rw [hEq]
      have hm :
          (⟨n + 1 - (⟨jv + 1, hj⟩ : Fin (n + 2)).val, by
            have h : (⟨jv + 1, hj⟩ : Fin (n + 2)).val = jv + 1 := rfl
            omega⟩ : Fin (n + 2)) =
          (⟨n - jv, by omega⟩ : Fin (n + 1)).castSucc := by
        apply Fin.ext
        change n + 1 - (jv + 1) = ((⟨n - jv, by omega⟩ : Fin (n + 1)).castSucc).val
        change n + 1 - (jv + 1) = n - jv
        omega
      rw [hM, hm, powTupleGen_succ_fst,
        powTupleGen_succ_fst (X := X) (n := n) (y := y),
        tupleInsAt_snoc, Fin.snoc_inj]
      refine ⟨?_, ?_⟩
      · exact ih _ (⟨jv, by omega⟩ : Fin (n + 1)) y
      · rw [genEtaSnd G n _ (⟨jv, by omega⟩ : Fin (n + 1)) y]

/-- Tuple coordinates of the opposite-monoid nerve.

A chain of n composable arrows in the one-object category of Gᵐᵒᵖ is equivalent to a tuple Fin
n → G in arrow order. -/
noncomputable abbrev nerveTupleEquiv (n : ℕ) :
    ComposableArrows (SingleObj Gᵐᵒᵖ) n ≃ (Fin n → G) :=
  nerve.singleObjOppEquiv G n

/-- The face and degeneracy data of the opposite-monoid nerve.

In degree n the object is the set of chains of n arrows in SingleObj Gᵐᵒᵖ. Faces and
degeneracies are the maps of its nerve, with their simplicial identities. -/
noncomputable def nerveOppData : SimplicialObject.Data (Type u) where
  obj := fun n => ComposableArrows (SingleObj Gᵐᵒᵖ) n
  δ := fun {n} i => (nerve (SingleObj Gᵐᵒᵖ)).map (SimplexCategory.δ i).op
  σ := fun {n} i => (nerve (SingleObj Gᵐᵒᵖ)).map (SimplexCategory.σ i).op
  δ_comp_δ := by
    intro n i j h
    have inner : (SimplexCategory.δ j.succ).op ≫ (SimplexCategory.δ i).op =
        (SimplexCategory.δ i.castSucc).op ≫ (SimplexCategory.δ j).op := by
      simp only [← op_comp, SimplexCategory.δ_comp_δ h]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_comp _ _ _)
  δ_comp_σ_of_le := by
    intro n i j h
    have inner : (SimplexCategory.σ j.succ).op ≫ (SimplexCategory.δ i.castSucc).op =
        (SimplexCategory.δ i).op ≫ (SimplexCategory.σ j).op := by
      simp only [← op_comp, SimplexCategory.δ_comp_σ_of_le h]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_comp _ _ _)
  δ_comp_σ_self := by
    intro n i
    have inner : (SimplexCategory.σ i).op ≫ (SimplexCategory.δ i.castSucc).op =
        𝟙 (Opposite.op (SimplexCategory.mk n)) := by
      simp only [← op_comp, SimplexCategory.δ_comp_σ_self, op_id]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_id _ _)
  δ_comp_σ_succ := by
    intro n i
    have inner : (SimplexCategory.σ i).op ≫ (SimplexCategory.δ i.succ).op =
        𝟙 (Opposite.op (SimplexCategory.mk n)) := by
      simp only [← op_comp, SimplexCategory.δ_comp_σ_succ, op_id]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_id _ _)
  δ_comp_σ_of_gt := by
    intro n i j h
    have inner : (SimplexCategory.σ j.castSucc).op ≫ (SimplexCategory.δ i.succ).op =
        (SimplexCategory.δ i).op ≫ (SimplexCategory.σ j).op := by
      simp only [← op_comp, SimplexCategory.δ_comp_σ_of_gt h]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_comp _ _ _)
  σ_comp_σ := by
    intro n i j h
    have inner : (SimplexCategory.σ j).op ≫ (SimplexCategory.σ i.castSucc).op =
        (SimplexCategory.σ i).op ≫ (SimplexCategory.σ j.succ).op := by
      simp only [← op_comp, SimplexCategory.σ_comp_σ h]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_comp _ _ _)

/-- The evaluated cartesian classifying-bar data.

Evaluate the two-sided bar for the tensor monad G × − and the trivial point actions at an
object a of the discrete one-point index category. The result is simplicial data in types. -/
noncomputable def barEvalData (a : Discrete PUnit.{1}) :
    SimplicialObject.Data (Type u) :=
  (SimplicialObject.Data.evalFunctor a).obj
    (barData (tensorMonad G)
      (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
        (ractPt_assoc G))
      (leftPointModule G PUnit))

/-- Tuple coordinates of the evaluated classifying bar.

In degree n, the evaluated classifying-bar object is equivalent to Fin n → G after removing
its two point factors. -/
noncomputable def barTupleEquiv (a : Discrete PUnit.{1}) (n : ℕ) :
    (barEvalData G a).obj n ≃ (Fin n → G) :=
  (Equiv.punitProd _).trans (powTupleEquiv G n)

/-- The degreewise isomorphism from the bar to the nerve.

Identify the evaluated classifying bar with G-tuples, then identify those tuples with chains
in SingleObj Gᵐᵒᵖ. This gives an isomorphism in every degree n. -/
noncomputable def tupleIso (a : Discrete PUnit.{1}) (n : ℕ) :
    (barEvalData G a).obj n ≅ (nerveOppData G).obj n :=
  Equiv.toIso ((barTupleEquiv G a n).trans (nerveTupleEquiv G n).symm)

/-- Nerve-side zero-face tuple formula.

`δ 0` of `ofTuple t` drops the head (`Fin.tail`). Whisker precomposition,
`Fin`-thinness, and `Fin.succAbove_zero` are definitional and bridged by
`show`; the consecutive arrow then reads via `mkOfObjOfMapSucc_map_succ`
and cancels with `unop_op`. No induction: `ComposableArrows` maps do not
recurse on `n`. -/
private theorem nerveTuple_zero_face (n : ℕ) (t : Fin (n + 1) → G) :
    (nerveOppData G).δ (0 : Fin (n + 2)) ((nerveTupleEquiv G (n + 1)).symm t) =
      (nerveTupleEquiv G n).symm (Fin.tail t) := by
  apply (nerveTupleEquiv G n).injective
  rw [Equiv.apply_symm_apply]
  funext j
  have hF : ((nerveTupleEquiv G (n + 1)).symm t) =
      ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun k => MulOpposite.op (t k)) := rfl
  rw [hF]
  change MulOpposite.unop
      ((((nerveOppData G).δ (0 : Fin (n + 2)))
        (ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
          (fun k => MulOpposite.op (t k)))).map' j.val (j.val + 1)) =
    Fin.tail t j
  change MulOpposite.unop
      ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun k => MulOpposite.op (t k))).map' (j.val + 1) (j.val + 1 + 1)) =
    Fin.tail t j
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (j.val + 1) (by omega)]
  exact MulOpposite.unop_op _

/-- The degreewise bar equivalence reads through the generalized reader. -/
private theorem barTupleEquiv_gen_fst (a : Discrete PUnit.{1}) (n : ℕ)
    (w : (barEvalData G a).obj n) :
    (barTupleEquiv G a n) w =
      ((((powTupleGen G (PUnit.{u+1} : Type u) n)
        (((rCastOut G ((monadPow (tensorMonad G) n).obj PUnit))
          (Equiv.cast (by rfl) w)).2)).1)) := by
  simp only [barTupleEquiv, powTupleEquiv]
  rfl

/-- The zeroth bar face removes the first coordinate.

For a degree-(n+1) bar element with tuple t, its zeroth face has tuple Fin.tail t. -/
theorem barTuple_zero_face (a : Discrete PUnit.{1}) :
    ∀ (n : ℕ) (x : (barEvalData G a).obj (n + 1)),
      (barTupleEquiv G a n) (((barEvalData G a).δ (0 : Fin (n + 2))) x) =
        Fin.tail ((barTupleEquiv G a (n + 1)) x) := by
  intro n x
  have hδm : ((barEvalData G a).δ (0 : Fin (n + 2))) =
      rightActionPow (tensorMonad G)
        (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
          (ractPt_assoc G)) n PUnit := by
    simp only [barEvalData, SimplicialObject.Data.evalFunctor_obj_δ,
      barData_δ_app]
    exact barFaceApp_of_val_zero (by simp)
  rw [hδm, barTupleEquiv_gen_fst, barTupleEquiv_gen_fst]
  exact genZeroFst G n (PUnit.{u+1} : Type u)
    ((rCastOut G ((monadPow (tensorMonad G) (n + 1)).obj PUnit))
      (Equiv.cast (by rfl) x))

/-- The last bar face removes the last coordinate.

For a face index i with i = n+1 on a degree-(n+1) bar element, the tuple of its face is
Fin.init of the original tuple. -/
theorem barTuple_last_face (a : Discrete PUnit.{1}) (n : ℕ)
    (x : (barEvalData G a).obj (n + 1)) (i : Fin (n + 2))
    (hL : i.val = n + 1) :
    (barTupleEquiv G a n) (((barEvalData G a).δ i) x) =
      Fin.init ((barTupleEquiv G a (n + 1)) x) := by
  have hδ : ((barEvalData G a).δ i) =
      (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
        (ractPt_assoc G)).functor.map
        ((monadPow (tensorMonad G) n).map
          ((leftPointModule G PUnit).action.app a)) := by
    simp only [barEvalData, SimplicialObject.Data.evalFunctor_obj_δ,
      barData_δ_app]
    exact barFaceApp_of_val_last hL
  rw [hδ, barTupleEquiv_gen_fst, barTupleEquiv_gen_fst]
  exact genLastFst G n _ _
    ((leftPointModule G PUnit).action.app a)
    ((rCastOut G ((monadPow (tensorMonad G) (n + 1)).obj PUnit))
      (Equiv.cast (by rfl) x))

/-- An interior bar face multiplies adjacent coordinates.

For k : Fin n and face index i = k+1, the face of a degree-(n+1) bar element contracts tuple
entries k and k+1 by their product in that order. -/
theorem barTuple_middle_face (a : Discrete PUnit.{1}) (n : ℕ)
    (x : (barEvalData G a).obj (n + 1)) (k : Fin n) (i : Fin (n + 2))
    (hk : i.val = k.val + 1) :
    (barTupleEquiv G a n) (((barEvalData G a).δ i) x) =
      tupleMulAt G n ((barTupleEquiv G a (n + 1)) x) k := by
  have hδ : ((barEvalData G a).δ i) =
      (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
        (ractPt_assoc G)).functor.map
        (barMuAtPos (tensorMonad G) n k PUnit) := by
    simp only [barEvalData, SimplicialObject.Data.evalFunctor_obj_δ,
      barData_δ_app]
    exact barFaceApp_of_middle hk
  rw [hδ, barTupleEquiv_gen_fst, barTupleEquiv_gen_fst, barMuAtPos_rev]
  have hGen := genMuFst G n (PUnit.{u+1} : Type u) k.rev
    (((rCastOut G ((monadPow (tensorMonad G) (n + 1)).obj PUnit))
      (Equiv.cast (by rfl) x)).2)
  have hm : (⟨n - 1 - k.rev.val, by have := k.isLt; omega⟩ : Fin n) = k := by
    apply Fin.ext
    simp only [Fin.val_rev]
    have hklt := k.isLt
    omega
  rw [hm] at hGen
  exact hGen

/-- A bar degeneracy inserts the monoid identity.

For i : Fin (n+1), the i-th degeneracy of a degree-n bar element inserts 1 at tuple position
i. -/
theorem barTuple_degen (a : Discrete PUnit.{1}) (n : ℕ)
    (x : (barEvalData G a).obj n) (i : Fin (n + 1)) :
    (barTupleEquiv G a (n + 1)) (((barEvalData G a).σ i) x) =
      tupleInsAt G n ((barTupleEquiv G a n) x) i := by
  have hσ : ((barEvalData G a).σ i) =
      (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
        (ractPt_assoc G)).functor.map
        (barEtaAtPos (tensorMonad G) n i PUnit) := by
    simp only [barEvalData, SimplicialObject.Data.evalFunctor_obj_σ,
      barData_σ_app]
    exact barData_σ_app (tensorMonad G)
      (rightModuleOfRightAction PUnit G (ractPt G) (ractPt_one G)
        (ractPt_assoc G)) (leftPointModule G PUnit) i a
  rw [hσ, barTupleEquiv_gen_fst, barTupleEquiv_gen_fst, barEtaAtPos_rev]
  have hGen := genEtaFst G n (PUnit.{u+1} : Type u) i.rev
    (((rCastOut G ((monadPow (tensorMonad G) n).obj PUnit))
      (Equiv.cast (by rfl) x)).2)
  have hm : (⟨n - i.rev.val, by have := i.isLt; omega⟩ : Fin (n + 1)) = i := by
    apply Fin.ext
    simp only [Fin.val_rev]
    have hilt := i.isLt
    omega
  rw [hm] at hGen
  exact hGen

/-- Nerve-side last-face tuple formula.

`δ (last _)` of `ofTuple t` drops the tail (`Fin.init`). The last-face
inclusion is definitional on indices, bridged by `show`; the consecutive
arrow then reads via `mkOfObjOfMapSucc_map_succ` and cancels with
`unop_op`. No induction. -/
private theorem nerveTuple_last_face (n : ℕ) (t : Fin (n + 1) → G)
    (i : Fin (n + 2)) (hL : i.val = n + 1) :
    (nerveOppData G).δ i ((nerveTupleEquiv G (n + 1)).symm t) =
      (nerveTupleEquiv G n).symm (Fin.init t) := by
  apply (nerveTupleEquiv G n).injective
  rw [Equiv.apply_symm_apply]
  funext j
  have hF : ((nerveTupleEquiv G (n + 1)).symm t) =
      ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun k => MulOpposite.op (t k)) := rfl
  rw [hF]
  have hi : i = Fin.last (n + 1) := Fin.ext hL
  subst hi
  change MulOpposite.unop
      ((((nerveOppData G).δ (Fin.last (n + 1)))
        (ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
          (fun k => MulOpposite.op (t k)))).map' j.val (j.val + 1)) =
    Fin.init t j
  have hle1 : ((Fin.last (n + 1)).succAbove ⟨j.val, by omega⟩).val ≤
      ((Fin.last (n + 1)).succAbove ⟨j.val + 1, by omega⟩).val := by
    rw [Fin.succAbove_last_apply, Fin.succAbove_last_apply]
    exact Nat.le_succ _
  have hle2 : ((Fin.last (n + 1)).succAbove ⟨j.val + 1, by omega⟩).val ≤
      n + 1 := by
    rw [Fin.succAbove_last_apply]
    omega
  have hδmap : ((((nerveOppData G).δ (Fin.last (n + 1)))
      (ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun k => MulOpposite.op (t k)))).map' j.val (j.val + 1)) =
      ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun k => MulOpposite.op (t k))).map'
        ((Fin.last (n + 1)).succAbove ⟨j.val, by omega⟩).val
        ((Fin.last (n + 1)).succAbove ⟨j.val + 1, by omega⟩).val
        hle1 hle2) := rfl
  have hS1 : ((Fin.last (n + 1)).succAbove ⟨j.val, by omega⟩) =
      Fin.castSucc ⟨j.val, by omega⟩ :=
    Fin.succAbove_last_apply _
  have hS2 : ((Fin.last (n + 1)).succAbove ⟨j.val + 1, by omega⟩) =
      Fin.castSucc ⟨j.val + 1, by omega⟩ :=
    Fin.succAbove_last_apply _
  rw [hδmap]
  clear hδmap
  revert hle1 hle2
  generalize hS1v : ((Fin.last (n + 1)).succAbove ⟨j.val, by omega⟩).val = s1
  generalize hS2v : ((Fin.last (n + 1)).succAbove ⟨j.val + 1, by omega⟩).val = s2
  intro _ _
  have e1 : s1 =
      (Fin.castSucc (⟨j.val, Nat.lt_succ_of_le j.isLt.le⟩ : Fin (n + 1))).val :=
    hS1v.symm.trans (congrArg Fin.val hS1)
  subst e1
  have e2 : s2 =
      (Fin.castSucc (⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ : Fin (n + 1))).val :=
    hS2v.symm.trans (congrArg Fin.val hS2)
  subst e2
  change MulOpposite.unop
      ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun k => MulOpposite.op (t k))).map' j.val (j.val + 1) (by omega)
        (by omega)) =
    Fin.init t j
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ j.val (by omega)]
  exact MulOpposite.unop_op _

/-- Nerve-side middle-face tuple formula.

`δ i` with `i.val = k.val + 1` composes the two adjacent nerve arrows:
below it keeps entries, at `k` it multiplies the consecutive pair (the
`Gᵐᵒᵖ` order via `SingleObj.comp_as_mul` agrees with bar multiplication),
and above it shifts down. The face inclusion acts by `Fin.succAbove`,
bridged explicitly with `succAbove_succ_of_le/of_lt`; the consecutive
arrow then reads via `mkOfObjOfMapSucc_map_succ` and cancels with
`unop_op`. No induction. -/
private theorem nerveTuple_middle_face (n : ℕ) (t : Fin (n + 1) → G)
    (k : Fin n) (i : Fin (n + 2)) (hk : i.val = k.val + 1) :
    (nerveOppData G).δ i ((nerveTupleEquiv G (n + 1)).symm t) =
      (nerveTupleEquiv G n).symm (tupleMulAt G n t k) := by
  apply (nerveTupleEquiv G n).injective
  rw [Equiv.apply_symm_apply]
  funext j
  have hF : ((nerveTupleEquiv G (n + 1)).symm t) =
      ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun l => MulOpposite.op (t l)) := rfl
  rw [hF]
  have hi : i = k.castSucc.succ := by
    apply Fin.ext
    change i.val = (k.castSucc.succ).val
    rw [Fin.val_succ, Fin.val_castSucc, hk]
  subst hi
  have hle1 : ((k.castSucc.succ.succAbove ⟨j.val, by omega⟩).val ≤
      (k.castSucc.succ.succAbove ⟨j.val + 1, by omega⟩).val) := by
    have h : (⟨j.val, by omega⟩ : Fin (n + 1)) ≤ ⟨j.val + 1, by omega⟩ := by
      simp
    exact Fin.le_def.mp (Fin.succAbove_le_succAbove_iff.mpr h)
  have hle2 : ((k.castSucc.succ.succAbove ⟨j.val + 1, by omega⟩).val ≤
      n + 1) := by
    have h := (k.castSucc.succ.succAbove ⟨j.val + 1, by omega⟩).isLt
    omega
  have hδmap : ((((nerveOppData G).δ (k.castSucc.succ))
      (ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun l => MulOpposite.op (t l)))).map' j.val (j.val + 1)) =
      ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun l => MulOpposite.op (t l))).map'
        (k.castSucc.succ.succAbove ⟨j.val, by omega⟩).val
        (k.castSucc.succ.succAbove ⟨j.val + 1, by omega⟩).val
        hle1 hle2) := rfl
  change MulOpposite.unop
      ((((nerveOppData G).δ (k.castSucc.succ))
        (ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
          (fun l => MulOpposite.op (t l)))).map' j.val (j.val + 1)) =
    tupleMulAt G n t k j
  rw [hδmap]
  clear hδmap
  by_cases hj1 : j.val < k.val
  · have ha : k.castSucc.succ.succAbove (⟨j.val, by omega⟩ : Fin (n + 1)) =
        Fin.castSucc (⟨j.val, by omega⟩ : Fin (n + 1)) := by
      apply Fin.succAbove_succ_of_le
      simp only [Fin.le_def, Fin.val_castSucc]
      omega
    have hb : k.castSucc.succ.succAbove (⟨j.val + 1, by omega⟩ : Fin (n + 1)) =
        Fin.castSucc (⟨j.val + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.succAbove_succ_of_le
      simp only [Fin.le_def, Fin.val_castSucc]
      omega
    revert hle1 hle2
    generalize hS1v : ((k.castSucc.succ.succAbove ⟨j.val, by omega⟩).val) = s1
    generalize hS2v : ((k.castSucc.succ.succAbove ⟨j.val + 1, by omega⟩).val) = s2
    intro _ _
    have e1 : s1 = j.val :=
      hS1v.symm.trans ((congrArg Fin.val ha).trans (Fin.val_castSucc _))
    subst e1
    have e2 : s2 = j.val + 1 :=
      hS2v.symm.trans ((congrArg Fin.val hb).trans (Fin.val_castSucc _))
    subst e2
    change MulOpposite.unop
        ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
          (fun l => MulOpposite.op (t l))).map' j.val (j.val + 1) (by omega)
          (by omega)) =
      tupleMulAt G n t k j
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ j.val (by omega),
      MulOpposite.unop_op]
    simp only [tupleMulAt]
    rw [Fin.contractNth_apply_of_lt _ _ _ _ hj1]
    rfl
  · by_cases hj2 : j.val = k.val
    · have hjk : k = j := Eq.symm (Fin.ext hj2)
      subst hjk
      have ha : k.castSucc.succ.succAbove (⟨k.val, by omega⟩ : Fin (n + 1)) =
          Fin.castSucc (⟨k.val, by omega⟩ : Fin (n + 1)) := by
        apply Fin.succAbove_succ_of_le
        simp only [Fin.le_def, Fin.val_castSucc]
        omega
      have hb : k.castSucc.succ.succAbove (⟨k.val + 1, by omega⟩ : Fin (n + 1)) =
          Fin.succ (⟨k.val + 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.succAbove_succ_of_lt
        simp only [Fin.lt_def, Fin.val_castSucc]
        omega
      revert hle1 hle2
      generalize hS1v : ((k.castSucc.succ.succAbove ⟨k.val, by omega⟩).val) = s1
      generalize hS2v : ((k.castSucc.succ.succAbove ⟨k.val + 1, by omega⟩).val) = s2
      intro _ _
      have e1 : s1 = k.val :=
        hS1v.symm.trans ((congrArg Fin.val ha).trans (Fin.val_castSucc _))
      subst e1
      have e2 : s2 = k.val + 1 + 1 :=
        hS2v.symm.trans ((congrArg Fin.val hb).trans (Fin.val_succ _))
      subst e2
      change MulOpposite.unop
          ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
            (fun l => MulOpposite.op (t l))).map' k.val (k.val + 1 + 1)
            (by omega) (by omega)) =
        tupleMulAt G n t k k
      rw [ComposableArrows.map'_comp _ k.val (k.val + 1) (k.val + 1 + 1)
        (by omega) (by omega) (by omega),
        ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k.val (by omega),
        ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (k.val + 1) (by omega),
        SingleObj.comp_as_mul, ← MulOpposite.op_mul, MulOpposite.unop_op]
      simp only [tupleMulAt]
      rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
      rfl
    · have ha : k.castSucc.succ.succAbove (⟨j.val, by omega⟩ : Fin (n + 1)) =
          Fin.succ (⟨j.val, by omega⟩ : Fin (n + 1)) := by
        apply Fin.succAbove_succ_of_lt
        simp only [Fin.lt_def, Fin.val_castSucc]
        omega
      have hb : k.castSucc.succ.succAbove (⟨j.val + 1, by omega⟩ : Fin (n + 1)) =
          Fin.succ (⟨j.val + 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.succAbove_succ_of_lt
        simp only [Fin.lt_def, Fin.val_castSucc]
        omega
      revert hle1 hle2
      generalize hS1v : ((k.castSucc.succ.succAbove ⟨j.val, by omega⟩).val) = s1
      generalize hS2v : ((k.castSucc.succ.succAbove ⟨j.val + 1, by omega⟩).val) = s2
      intro _ _
      have e1 : s1 = j.val + 1 :=
        hS1v.symm.trans ((congrArg Fin.val ha).trans (Fin.val_succ _))
      subst e1
      have e2 : s2 = j.val + 1 + 1 :=
        hS2v.symm.trans ((congrArg Fin.val hb).trans (Fin.val_succ _))
      subst e2
      change MulOpposite.unop
          ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
            (fun l => MulOpposite.op (t l))).map' (j.val + 1) (j.val + 1 + 1)
            (by omega) (by omega)) =
        tupleMulAt G n t k j
      have hlt : k.val < j.val := by omega
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (j.val + 1) (by omega),
        MulOpposite.unop_op]
      simp only [tupleMulAt]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ hlt]
      rfl

/-- Nerve-side degeneracy tuple formula.

`σ i` of `ofTuple t` inserts `1` at `i` (`tupleInsAt`): below it keeps
entries, at `i` the pulled-back consecutive arrow is degenerate (`map'_self`,
with `1` via `unop`), and above it shifts down. The degeneracy inclusion acts
by `Fin.predAbove`, bridged explicitly with `predAbove_of_le_castSucc`/
`predAbove_of_castSucc_lt`; the consecutive arrow then reads via
`mkOfObjOfMapSucc_map_succ` and cancels with `unop_op`. No induction. -/
private theorem nerveTuple_degen (n : ℕ) (t : Fin n → G) (i : Fin (n + 1)) :
    (nerveOppData G).σ i ((nerveTupleEquiv G n).symm t) =
      (nerveTupleEquiv G (n + 1)).symm (tupleInsAt G n t i) := by
  apply (nerveTupleEquiv G (n + 1)).injective
  rw [Equiv.apply_symm_apply]
  funext j
  have hF : ((nerveTupleEquiv G n).symm t) =
      ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun l => MulOpposite.op (t l)) := rfl
  rw [hF]
  have hle1 : ((i.predAbove ⟨j.val, by omega⟩).val ≤
      (i.predAbove ⟨j.val + 1, by omega⟩).val) := by
    have h : (⟨j.val, by omega⟩ : Fin (n + 2)) ≤ ⟨j.val + 1, by omega⟩ := by
      simp
    exact Fin.le_def.mp ((Fin.predAbove_right_monotone i) h)
  have hle2 : ((i.predAbove ⟨j.val + 1, by omega⟩).val ≤ n) := by
    have h := (i.predAbove ⟨j.val + 1, by omega⟩).isLt
    omega
  have hσmap : ((((nerveOppData G).σ i)
      (ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun l => MulOpposite.op (t l)))).map' j.val (j.val + 1)) =
      ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
        (fun l => MulOpposite.op (t l))).map'
        (i.predAbove ⟨j.val, by omega⟩).val
        (i.predAbove ⟨j.val + 1, by omega⟩).val
        hle1 hle2) := rfl
  change MulOpposite.unop
      ((((nerveOppData G).σ i)
        (ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
          (fun l => MulOpposite.op (t l)))).map' j.val (j.val + 1)) =
    tupleInsAt G n t i j
  rw [hσmap]
  clear hσmap
  by_cases hj1 : j.val < i.val
  · have hside1 : (⟨j.val, by omega⟩ : Fin (n + 2)) ≤ i.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc]
      omega
    have ha := Fin.predAbove_of_le_castSucc i _ hside1
    have hside2 : (⟨j.val + 1, by omega⟩ : Fin (n + 2)) ≤ i.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc]
      omega
    have hb := Fin.predAbove_of_le_castSucc i _ hside2
    revert hle1 hle2
    generalize hS1v : ((i.predAbove ⟨j.val, by omega⟩).val) = s1
    generalize hS2v : ((i.predAbove ⟨j.val + 1, by omega⟩).val) = s2
    intro _ _
    have e1 : s1 = j.val :=
      hS1v.symm.trans ((congrArg Fin.val ha).trans (Fin.coe_castPred _ _))
    subst e1
    have e2 : s2 = j.val + 1 :=
      hS2v.symm.trans ((congrArg Fin.val hb).trans (Fin.coe_castPred _ _))
    subst e2
    change MulOpposite.unop
        ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
          (fun l => MulOpposite.op (t l))).map' j.val (j.val + 1) (by omega)
          (by omega)) =
      tupleInsAt G n t i j
    have hInsBelow : tupleInsAt G n t i j =
        t ⟨j.val, by have := i.isLt; omega⟩ := by
      simp only [tupleInsAt]
      rw [Fin.insertNth_apply_below (Fin.lt_def.mpr hj1)]
      simp
      congr 1
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ j.val (by omega),
      MulOpposite.unop_op, hInsBelow]
  · by_cases hj2 : j.val = i.val
    · have hji : i = j := Eq.symm (Fin.ext hj2)
      subst hji
      have hside1 : (⟨i.val, by omega⟩ : Fin (n + 2)) ≤ i.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc]
        omega
      have ha := Fin.predAbove_of_le_castSucc i _ hside1
      have hside2 : i.castSucc < (⟨i.val + 1, by omega⟩ : Fin (n + 2)) := by
        simp only [Fin.lt_def, Fin.val_castSucc]
        omega
      have hb := Fin.predAbove_of_castSucc_lt i _ hside2
      revert hle1 hle2
      generalize hS1v : ((i.predAbove ⟨i.val, by omega⟩).val) = s1
      generalize hS2v : ((i.predAbove ⟨i.val + 1, by omega⟩).val) = s2
      intro _ _
      have e1 : s1 = i.val :=
        hS1v.symm.trans ((congrArg Fin.val ha).trans (Fin.coe_castPred _ _))
      subst e1
      have e2 : s2 = i.val :=
        hS2v.symm.trans ((congrArg Fin.val hb).trans (Fin.val_pred _ _))
      subst e2
      change MulOpposite.unop
          ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
            (fun l => MulOpposite.op (t l))).map' i.val i.val (by omega)
            (by omega)) =
        tupleInsAt G n t i i
      have hInsAt : tupleInsAt G n t i i = 1 := by
        simp only [tupleInsAt]
        rw [Fin.insertNth_apply_same]
      rw [ComposableArrows.map'_self _ _ (by omega), hInsAt]
      exact MulOpposite.unop_one
    · have hside1 : i.castSucc < (⟨j.val, by omega⟩ : Fin (n + 2)) := by
        simp only [Fin.lt_def, Fin.val_castSucc]
        omega
      have ha := Fin.predAbove_of_castSucc_lt i _ hside1
      have hside2 : i.castSucc < (⟨j.val + 1, by omega⟩ : Fin (n + 2)) := by
        simp only [Fin.lt_def, Fin.val_castSucc]
        omega
      have hb := Fin.predAbove_of_castSucc_lt i _ hside2
      revert hle1 hle2
      generalize hS1v : ((i.predAbove ⟨j.val, by omega⟩).val) = s1
      generalize hS2v : ((i.predAbove ⟨j.val + 1, by omega⟩).val) = s2
      intro _ _
      have e1 : s1 = j.val - 1 :=
        hS1v.symm.trans ((congrArg Fin.val ha).trans (Fin.val_pred _ _))
      subst e1
      have h2 : (i.predAbove ⟨j.val + 1, by omega⟩).val = j.val + 1 - 1 := by
        rw [hb, Fin.val_pred _ (by simp)]
      have e2 : s2 = j.val - 1 + 1 := by omega
      subst e2
      change MulOpposite.unop
          ((ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Gᵐᵒᵖ)
            (fun l => MulOpposite.op (t l))).map' (j.val - 1) (j.val - 1 + 1)
            (by omega) (by omega)) =
        tupleInsAt G n t i j
      have hInsAbove : tupleInsAt G n t i j =
          t ⟨j.val - 1, by have := j.isLt; omega⟩ := by
        have hlt : i < j := Fin.lt_def.mpr (by omega : i.val < j.val)
        simp only [tupleInsAt]
        rw [Fin.insertNth_apply_above hlt]
        simp
        congr 1
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (j.val - 1) (by omega),
        MulOpposite.unop_op, hInsAbove]

/-- The bar-to-nerve comparison commutes with every face.

For each i : Fin (n+2), applying the degree-(n+1) comparison then the nerve face equals
applying the bar face then the degree-n comparison. -/
theorem tupleIso_face (a : Discrete PUnit.{1}) {n : ℕ} (i : Fin (n + 2)) :
    (tupleIso G a (n + 1)).hom ≫ (nerveOppData G).δ i =
      (barEvalData G a).δ i ≫ (tupleIso G a n).hom := by
  ext x
  change (ConcreteCategory.hom ((tupleIso G a (n + 1)).hom ≫ (nerveOppData G).δ i)) x =
    (ConcreteCategory.hom ((barEvalData G a).δ i ≫ (tupleIso G a n).hom)) x
  change (ConcreteCategory.hom ((nerveOppData G).δ i))
        (((barTupleEquiv G a (n + 1)).trans (nerveTupleEquiv G (n + 1)).symm) x) =
      ((barTupleEquiv G a n).trans (nerveTupleEquiv G n).symm)
        ((ConcreteCategory.hom ((barEvalData G a).δ i)) x)
  by_cases h0 : i.val = 0
  · have hi0 : i = 0 := Fin.ext h0
    subst hi0
    have hL := nerveTuple_zero_face G n ((barTupleEquiv G a (n + 1)) x)
    have hR := barTuple_zero_face G a n x
    change ((nerveOppData G).δ (0 : Fin (n + 2)))
          ((nerveTupleEquiv G (n + 1)).symm
            ((barTupleEquiv G a (n + 1)) x)) =
        ((nerveTupleEquiv G n).symm
          ((barTupleEquiv G a n) (((barEvalData G a).δ (0 : Fin (n + 2))) x)))
    rw [hL, hR]
  · by_cases hL : i.val = n + 1
    · have hLn := nerveTuple_last_face G n ((barTupleEquiv G a (n + 1)) x) i hL
      have hR := barTuple_last_face G a n x i hL
      change ((nerveOppData G).δ i)
            ((nerveTupleEquiv G (n + 1)).symm
              ((barTupleEquiv G a (n + 1)) x)) =
          ((nerveTupleEquiv G n).symm
            ((barTupleEquiv G a n) (((barEvalData G a).δ i) x)))
      rw [hLn, hR]
    · obtain ⟨k, hk⟩ : ∃ k : Fin n, i.val = k.val + 1 :=
        ⟨⟨i.val - 1, by omega⟩, by change i.val = i.val - 1 + 1; omega⟩
      have hLn := nerveTuple_middle_face G n ((barTupleEquiv G a (n + 1)) x) k i hk
      have hR := barTuple_middle_face G a n x k i hk
      change ((nerveOppData G).δ i)
            ((nerveTupleEquiv G (n + 1)).symm
              ((barTupleEquiv G a (n + 1)) x)) =
          ((nerveTupleEquiv G n).symm
            ((barTupleEquiv G a n) (((barEvalData G a).δ i) x)))
      rw [hLn, hR]

/-- The bar-to-nerve comparison commutes with every degeneracy.

For each i : Fin (n+1), applying the degree-n comparison then the nerve degeneracy equals
applying the bar degeneracy then the degree-(n+1) comparison. -/
theorem tupleIso_degeneracy (a : Discrete PUnit.{1}) {n : ℕ}
    (i : Fin (n + 1)) :
    (tupleIso G a n).hom ≫ (nerveOppData G).σ i =
      (barEvalData G a).σ i ≫ (tupleIso G a (n + 1)).hom := by
  ext x
  change (ConcreteCategory.hom ((tupleIso G a n).hom ≫ (nerveOppData G).σ i)) x =
    (ConcreteCategory.hom ((barEvalData G a).σ i ≫ (tupleIso G a (n + 1)).hom)) x
  change (ConcreteCategory.hom ((nerveOppData G).σ i))
        (((barTupleEquiv G a n).trans (nerveTupleEquiv G n).symm) x) =
      ((barTupleEquiv G a (n + 1)).trans (nerveTupleEquiv G (n + 1)).symm)
        ((ConcreteCategory.hom ((barEvalData G a).σ i)) x)
  have hLn := nerveTuple_degen G n ((barTupleEquiv G a n) x) i
  have hR := barTuple_degen G a n x i
  change ((nerveOppData G).σ i)
        ((nerveTupleEquiv G n).symm
          ((barTupleEquiv G a n) x)) =
      ((nerveTupleEquiv G (n + 1)).symm
        ((barTupleEquiv G a (n + 1)) (((barEvalData G a).σ i) x)))
  rw [hLn, hR]

/-- An isomorphism of classifying-bar and nerve data.

For any monoid G, the evaluated cartesian classifying-bar data is isomorphic to the nerve data
of SingleObj Gᵐᵒᵖ. The degreewise tuple comparison respects all faces and degeneracies. -/
noncomputable def classifyingNerveDataIso (a : Discrete PUnit.{1}) :
    barEvalData G a ≅ nerveOppData G :=
  SimplicialObject.Data.isoOfIso (tupleIso G a)
    (fun i => tupleIso_face G a i) (fun i => tupleIso_degeneracy G a i)

end Monad
end CategoryTheory
