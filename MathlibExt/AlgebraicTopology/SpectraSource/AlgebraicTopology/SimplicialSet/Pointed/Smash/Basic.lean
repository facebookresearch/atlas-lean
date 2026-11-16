/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialSet/Pointed/Smash/Basic.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Basic
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Category.Pointed.Smash.Basic

-- The simplices of the smash product are classes of pairs only after unfolding the
-- pointed smash and the pointed-simplicial equivalence, whose bodies are not exposed.
import all MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Basic
import all MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Category.Pointed.Smash.Basic

/-!
# The smash product of pointed simplicial sets

The smash product `X ∧ Y` of pointed simplicial sets is the degreewise smash product of pointed
types: its `n`-simplices are the classes of pairs of `n`-simplices of `X` and `Y`, with every
pair having a coordinate at the basepoint collapsed to the basepoint. Equivalently it is the
degreewise quotient of the cartesian product `X × Y` by the wedge `X ∨ Y`. With unit
`S⁰ = Δ[0]₊`, the smash product makes `PointedSSet` a symmetric monoidal category, whose
braiding swaps the two factors.

The monoidal structure is transported from the pointwise smash product of simplicial objects in
`Pointed` along `PointedSSet.simplicialPointedEquivalence`, so all coherence equations come from
those of `Pointed`. This file supplies the simplex-level description of the structure.

## Main definitions

* `PointedSSet.smashMk x y`: the class in `X ⊗ Y` of a pair of simplices of the same degree.
* `PointedSSet.tensorUnitSimplex n`: the non-basepoint `n`-simplex of the unit `S⁰`.
* `PointedSSet.smashLift`: the based map out of `X ⊗ Y` induced by a simplicial map out of
  the cartesian product sending the wedge to the basepoint.
* `PointedSSet.wedge X Y`: the wedge `X ∨ Y`, as a subcomplex of the cartesian product.
* `PointedSSet.smashProj X Y`: the quotient map from the cartesian product onto `X ⊗ Y`.

## Main statements

* The instances `MonoidalCategory PointedSSet` and `SymmetricCategory PointedSSet`.
* `PointedSSet.tensor_ext`: based maps out of `X ⊗ Y` are determined on classes of pairs.
* `PointedSSet.isPushout_smashProj`: `X ⊗ Y` is the pushout of `X × Y ← X ∨ Y → Δ[0]`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

universe u

open CategoryTheory MonoidalCategory Monoidal Limits Simplicial

namespace MathlibExt.SpectraSource

namespace PointedSSet

/-- The degreewise smash product makes pointed simplicial sets a monoidal category, with unit
`S⁰ = Δ[0]₊`. -/
instance monoidalCategory : MonoidalCategory PointedSSet.{u} :=
  inferInstanceAs (MonoidalCategory (Transported simplicialPointedEquivalence.{u}.symm))

/-- The swap of factors makes the degreewise smash product symmetric monoidal. -/
instance symmetricCategory : SymmetricCategory PointedSSet.{u} :=
  inferInstanceAs (SymmetricCategory (Transported simplicialPointedEquivalence.{u}.symm))

/-- The degreewise pointed presentation is strong monoidal for the smash product. -/
noncomputable instance simplicialPointedEquivalenceMonoidal :
    simplicialPointedEquivalence.{u}.functor.Monoidal :=
  inferInstanceAs
    (Monoidal.equivalenceTransported simplicialPointedEquivalence.{u}.symm).inverse.Monoidal

/-- The tensor comparison is the inverse counit on the degreewise smash product. -/
@[simp]
lemma simplicialPointedEquivalence_μ (X Y : PointedSSet.{u}) :
    Functor.LaxMonoidal.μ simplicialPointedEquivalence.functor X Y =
      simplicialPointedEquivalence.counitIso.inv.app
        (simplicialPointedEquivalence.functor.obj X ⊗
          simplicialPointedEquivalence.functor.obj Y) := (rfl)

/-- The inverse tensor comparison is the counit on the degreewise smash product. -/
@[simp]
lemma simplicialPointedEquivalence_δ (X Y : PointedSSet.{u}) :
    Functor.OplaxMonoidal.δ simplicialPointedEquivalence.functor X Y =
      simplicialPointedEquivalence.counitIso.hom.app
        (simplicialPointedEquivalence.functor.obj X ⊗
          simplicialPointedEquivalence.functor.obj Y) := (rfl)

/-- The unit comparison is the inverse counit on the constant pointed unit. -/
@[simp]
lemma simplicialPointedEquivalence_ε :
    Functor.LaxMonoidal.ε simplicialPointedEquivalence.{u}.functor =
      simplicialPointedEquivalence.counitIso.inv.app (𝟙_ (SimplicialObject Pointed.{u})) := (rfl)

/-- The inverse unit comparison is the counit on the constant pointed unit. -/
@[simp]
lemma simplicialPointedEquivalence_η :
    Functor.OplaxMonoidal.η simplicialPointedEquivalence.{u}.functor =
      simplicialPointedEquivalence.counitIso.hom.app (𝟙_ (SimplicialObject Pointed.{u})) := (rfl)

variable {X Y Z X' Y' : PointedSSet.{u}} {n m : SimplexCategoryᵒᵖ}

/-- The class in the smash product `X ⊗ Y` of a pair of simplices of the same degree. -/
def smashMk (x : X.right.obj n) (y : Y.right.obj n) : (X ⊗ Y).right.obj n :=
  Pointed.smash.mk (X := Pointed.of (X.point n)) (Y := Pointed.of (Y.point n)) x y

lemma smashMk_surjective :
    Function.Surjective (fun p : X.right.obj n × Y.right.obj n ↦ smashMk p.1 p.2) :=
  Pointed.smash.mk_surjective

/-- Induction on the simplices of a smash product: it suffices to treat classes of pairs. -/
@[elab_as_elim]
lemma smashMk_induction {motive : (X ⊗ Y).right.obj n → Prop}
    (h : ∀ x y, motive (smashMk x y)) (a : (X ⊗ Y).right.obj n) : motive a :=
  Pointed.smash.ind h a

@[simp]
lemma map_smashMk (f : n ⟶ m) (x : X.right.obj n) (y : Y.right.obj n) :
    (X ⊗ Y).right.map f (smashMk x y) = smashMk (X.right.map f x) (Y.right.map f y) := (rfl)

lemma point_tensorObj (n : SimplexCategoryᵒᵖ) :
    (X ⊗ Y).point n = smashMk (X.point n) (Y.point n) := (rfl)

/-- Two pairs have the same class exactly when they are equal or both lie in the wedge. -/
lemma smashMk_eq_smashMk_iff {x x' : X.right.obj n} {y y' : Y.right.obj n} :
    smashMk x y = smashMk x' y' ↔
      x = x' ∧ y = y' ∨ (x = X.point n ∨ y = Y.point n) ∧ (x' = X.point n ∨ y' = Y.point n) :=
  Pointed.smash.mk_eq_mk_iff

/-- A pair represents the basepoint exactly when it lies in the wedge. -/
@[simp]
lemma smashMk_eq_point_iff {x : X.right.obj n} {y : Y.right.obj n} :
    smashMk x y = (X ⊗ Y).point n ↔ x = X.point n ∨ y = Y.point n :=
  Pointed.smash.mk_eq_point_iff

@[simp]
lemma smashMk_point_left (y : Y.right.obj n) : smashMk (X.point n) y = (X ⊗ Y).point n :=
  smashMk_eq_point_iff.2 (.inl rfl)

@[simp]
lemma smashMk_point_right (x : X.right.obj n) : smashMk x (Y.point n) = (X ⊗ Y).point n :=
  smashMk_eq_point_iff.2 (.inr rfl)

/-- Based maps out of a smash product are determined by their values on classes of pairs. -/
@[ext]
lemma tensor_ext {f g : X ⊗ Y ⟶ Z}
    (h : ∀ n x y, f.right.app n (smashMk x y) = g.right.app n (smashMk x y)) : f = g := by
  ext n a
  induction a using smashMk_induction
  exact h _ _ _

@[simp]
lemma tensorHom_app_smashMk (f : X ⟶ X') (g : Y ⟶ Y') (x : X.right.obj n)
    (y : Y.right.obj n) :
    (f ⊗ₘ g).right.app n (smashMk x y) = smashMk (f.right.app n x) (g.right.app n y) := (rfl)

@[simp]
lemma whiskerLeft_app_smashMk (g : Y ⟶ Y') (x : X.right.obj n) (y : Y.right.obj n) :
    (X ◁ g).right.app n (smashMk x y) = smashMk x (g.right.app n y) := (rfl)

@[simp]
lemma whiskerRight_app_smashMk (f : X ⟶ X') (x : X.right.obj n) (y : Y.right.obj n) :
    (f ▷ Y).right.app n (smashMk x y) = smashMk (f.right.app n x) y := (rfl)

@[simp]
lemma associator_hom_app_smashMk (x : X.right.obj n) (y : Y.right.obj n)
    (z : Z.right.obj n) :
    (α_ X Y Z).hom.right.app n (smashMk (smashMk x y) z) = smashMk x (smashMk y z) := (rfl)

@[simp]
lemma associator_inv_app_smashMk (x : X.right.obj n) (y : Y.right.obj n)
    (z : Z.right.obj n) :
    (α_ X Y Z).inv.right.app n (smashMk x (smashMk y z)) = smashMk (smashMk x y) z := (rfl)

@[simp]
lemma braiding_hom_app_smashMk (x : X.right.obj n) (y : Y.right.obj n) :
    (β_ X Y).hom.right.app n (smashMk x y) = smashMk y x := (rfl)

@[simp]
lemma braiding_inv_app_smashMk (x : X.right.obj n) (y : Y.right.obj n) :
    (β_ X Y).inv.right.app n (smashMk y x) = smashMk x y := (rfl)

/-! ### The unit `S⁰` -/

/-- The non-basepoint `n`-simplex of the unit `S⁰ = Δ[0]₊`. -/
-- The code generator cannot see through the unexposed equivalence giving the carrier.
noncomputable def tensorUnitSimplex (n : SimplexCategoryᵒᵖ) : (𝟙_ PointedSSet.{u}).right.obj n :=
  (some PUnit.unit : Option PUnit.{u + 1})

@[simp]
lemma tensorUnitSimplex_ne_point (n : SimplexCategoryᵒᵖ) :
    tensorUnitSimplex.{u} n ≠ (𝟙_ PointedSSet.{u}).point n :=
  Option.some_ne_none _

/-- Every simplex of the unit `S⁰` is the basepoint or the non-basepoint simplex. -/
lemma eq_point_or_eq_tensorUnitSimplex (s : (𝟙_ PointedSSet.{u}).right.obj n) :
    s = (𝟙_ PointedSSet.{u}).point n ∨ s = tensorUnitSimplex n := by
  rcases (s : Option PUnit.{u + 1}) with _ | ⟨⟨⟩⟩
  exacts [.inl rfl, .inr rfl]

@[simp]
lemma map_tensorUnitSimplex (f : n ⟶ m) :
    (𝟙_ PointedSSet.{u}).right.map f (tensorUnitSimplex n) = tensorUnitSimplex m := (rfl)

@[simp]
lemma leftUnitor_hom_app_smashMk (x : X.right.obj n) :
    (λ_ X).hom.right.app n (smashMk (tensorUnitSimplex n) x) = x := (rfl)

@[simp]
lemma leftUnitor_inv_app_apply (x : X.right.obj n) :
    (λ_ X).inv.right.app n x = smashMk (tensorUnitSimplex n) x := (rfl)

@[simp]
lemma rightUnitor_hom_app_smashMk (x : X.right.obj n) :
    (ρ_ X).hom.right.app n (smashMk x (tensorUnitSimplex n)) = x := (rfl)

@[simp]
lemma rightUnitor_inv_app_apply (x : X.right.obj n) :
    (ρ_ X).inv.right.app n x = smashMk x (tensorUnitSimplex n) := (rfl)

/-! ### The smash product as a quotient of the cartesian product -/

/-- The based map out of the smash product `X ⊗ Y` induced by a simplicial map out of the
cartesian product sending the wedge `X ∨ Y` to the basepoint. -/
def smashLift (f : X.right ⊗ Y.right ⟶ Z.right)
    (hl : ∀ n y, f.app n (X.point n, y) = Z.point n)
    (hr : ∀ n x, f.app n (x, Y.point n) = Z.point n) : X ⊗ Y ⟶ Z :=
  Under.homMk
    { app n := ↾(Pointed.smash.lift (Z := Pointed.of (Z.point n)) (fun x y ↦ f.app n (x, y))
        (hl n) (hr n)).toFun
      naturality n m g := by
        ext a
        induction a using smashMk_induction with | h x y
        exact NatTrans.naturality_apply f g ((x, y) : X.right.obj n × Y.right.obj n) }
    (by
      ext n a
      simp only [NatTrans.comp_app, TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply,
        ConcreteCategory.hom_ofHom, hom_app]
      exact hl n (Y.point n))

@[simp]
lemma smashLift_app_smashMk (f : X.right ⊗ Y.right ⟶ Z.right)
    (hl : ∀ n y, f.app n (X.point n, y) = Z.point n)
    (hr : ∀ n x, f.app n (x, Y.point n) = Z.point n) (x : X.right.obj n) (y : Y.right.obj n) :
    (smashLift f hl hr).right.app n (smashMk x y) = f.app n (x, y) := (rfl)

/-- The wedge `X ∨ Y`, as the subcomplex of the cartesian product `X × Y` of the pairs having a
coordinate at the basepoint. -/
def wedge (X Y : PointedSSet.{u}) : (X.right ⊗ Y.right).Subcomplex :=
  SSet.Subcomplex.unionProd (SSet.Subcomplex.range X.hom) (SSet.Subcomplex.range Y.hom)

/-- A simplex of the cartesian product lies in the wedge exactly when one of its coordinates is
the basepoint. -/
@[simp]
lemma mem_wedge_iff (z : (X.right ⊗ Y.right).obj n) :
    dsimp% z ∈ (wedge X Y).obj n ↔ z.1 = X.point n ∨ z.2 = Y.point n := by
  have h (W : PointedSSet.{u}) (w : W.right.obj n) :
      w ∈ (SSet.Subcomplex.range W.hom).obj n ↔ w = W.point n :=
    ⟨fun ⟨a, ha⟩ ↦ ha ▸ W.hom_app n a, fun hw ↦ ⟨SSet.stdSimplex.const 0 0 n, hw.symm⟩⟩
  exact (SSet.Subcomplex.mem_unionProd_iff _ _ z).trans (by rw [h, h, or_comm])

/-- The quotient map from the cartesian product `X × Y` onto the smash product `X ⊗ Y`. -/
def smashProj (X Y : PointedSSet.{u}) : X.right ⊗ Y.right ⟶ (X ⊗ Y).right where
  app n := ↾fun z ↦ smashMk z.1 z.2

@[simp]
lemma smashProj_app_apply (z : (X.right ⊗ Y.right).obj n) :
    dsimp% (smashProj X Y).app n z = smashMk z.1 z.2 := (rfl)

instance : Epi (smashProj X Y) := by
  rw [NatTrans.epi_iff_epi_app]
  exact fun n ↦ (epi_iff_surjective _).2 smashMk_surjective

@[reassoc (attr := simp)]
lemma smashProj_comp_smashLift (f : X.right ⊗ Y.right ⟶ Z.right)
    (hl : ∀ n y, f.app n (X.point n, y) = Z.point n)
    (hr : ∀ n x, f.app n (x, Y.point n) = Z.point n) :
    smashProj X Y ≫ (smashLift f hl hr).right = f := (rfl)

/-- The smash product `X ⊗ Y` is the quotient of the cartesian product `X × Y` collapsing the
wedge `X ∨ Y` to the basepoint. -/
lemma isPushout_smashProj :
    IsPushout (wedge X Y).ι (SSet.stdSimplex.isTerminalObj₀.from _) (smashProj X Y)
      (X ⊗ Y).hom := by
  have hw (s : PushoutCocone (wedge X Y).ι (SSet.stdSimplex.isTerminalObj₀.from _))
      (n : SimplexCategoryᵒᵖ) (z : (X.right ⊗ Y.right).obj n) (hz : z ∈ (wedge X Y).obj n) :
      s.inl.app n z = point (Under.mk s.inr) n :=
    (ConcreteCategory.congr_hom (congr_app s.condition n) ⟨z, hz⟩).trans
      (hom_app (Under.mk s.inr) n _)
  let desc (s : PushoutCocone (wedge X Y).ι (SSet.stdSimplex.isTerminalObj₀.from _)) :=
    smashLift (Z := Under.mk s.inr) s.inl
      (fun n _ ↦ hw s n _ ((mem_wedge_iff _).2 (.inl rfl)))
      (fun n _ ↦ hw s n _ ((mem_wedge_iff _).2 (.inr rfl)))
  refine .of_isColimit (PushoutCocone.IsColimit.mk ?_ (fun s ↦ (desc s).right)
    (fun s ↦ smashProj_comp_smashLift _ _ _) (fun s ↦ Under.w (desc s))
    fun s m h _ ↦ (cancel_epi (smashProj X Y)).1
      (h.trans (smashProj_comp_smashLift (Z := Under.mk s.inr) s.inl _ _).symm))
  ext n w
  exact (smashMk_eq_point_iff.2 ((mem_wedge_iff w.1).1 w.2)).trans
    (hom_app _ n ((SSet.stdSimplex.isTerminalObj₀.from _).app n w)).symm

end PointedSSet

end MathlibExt.SpectraSource
