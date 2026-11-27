/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Homotopy.HomotopyGroup
/-!
# Exact flags and the actual Waldhausen S-construction space

An S_n object is an actual diagram on the interval-arrow category of
Fin(n+1), with zero diagonals and genuine short exact subquotient sequences.
The specified object property restricts its terms. Isomorphisms of these
flags form the level groupoid. Restriction, the simplicial identities, the
nerve, its diagonal and exact-functor maps are constructed here.

The based geometric realization is therefore a fixed carrier for higher
exact-category groups. No category, spectrum, delooping or localization law
is supplied as an arbitrary model. The higher comparison laws remain work
for a separate Wanted module.

Reference: F. Waldhausen, *Algebraic K-theory of spaces*, in Algebraic and
Geometric Topology (1985), §1.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.WaldhausenExactFlags
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject Simplicial
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def interval {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : Arrow (Fin (n + 1)) :=
  Arrow.mk (homOfLE h)

def first {n : ℕ} {i j k : Fin (n + 1)} (h : i ≤ j) (h' : j ≤ k) :
    interval i j h ⟶ interval i k (h.trans h') := Arrow.homMk (𝟙 i) (homOfLE h')
def second {n : ℕ} {i j k : Fin (n + 1)} (h : i ≤ j) (h' : j ≤ k) :
    interval i k (h.trans h') ⟶ interval j k h' := Arrow.homMk (homOfLE h) (𝟙 k)

def IsSFlag (P : ObjectProperty C) (n : ℕ)
    (F : Arrow (Fin (n + 1)) ⥤ C) : Prop :=
  (∀ a, P (F.obj a)) ∧
  (∀ i, IsZero (F.obj (interval i i le_rfl))) ∧
  ∀ (i j k : Fin (n + 1)) (h : i ≤ j) (h' : j ≤ k),
    ∃ w : F.map (first h h') ≫ F.map (second h h') = 0,
      (ShortComplex.mk (F.map (first h h')) (F.map (second h h')) w).ShortExact

abbrev SLevel (P : ObjectProperty C) (n : ℕ) := ObjectProperty.FullSubcategory (IsSFlag P n)

def orderFunctor {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    Fin (m + 1) ⥤ Fin (n + 1) := α.monotone.functor

def restriction {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (F : Arrow (Fin (n + 1)) ⥤ C) : Arrow (Fin (m + 1)) ⥤ C :=
  (orderFunctor α).mapArrow ⋙ F

theorem restriction_isSFlag (P : ObjectProperty C) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (F : Arrow (Fin (n + 1)) ⥤ C)
    (hF : IsSFlag P n F) : IsSFlag P m (restriction α F) := by
  refine ⟨fun a => hF.1 _, fun i => hF.2.1 (α i), ?_⟩
  intro i j k h h'
  exact hF.2.2 (α i) (α j) (α k) (α.monotone h) (α.monotone h')

def restrictFunctor (P : ObjectProperty C) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) : SLevel P n ⥤ SLevel P m where
  obj F := ⟨restriction α F.obj, restriction_isSFlag P α F.obj F.property⟩
  map a := ObjectProperty.homMk (Functor.whiskerLeft (orderFunctor α).mapArrow a.hom)

def sConstruction (P : ObjectProperty C) : SimplexCategoryᵒᵖ ⥤ Cat.{v,max u v} where
  obj n := Cat.of (Core (SLevel P n.unop.len))
  map α := Cat.Hom.ofFunctor (restrictFunctor P α.unop.toOrderHom).core
  map_id n := by rfl
  map_comp α β := by rfl

abbrev bisimplicial (P : ObjectProperty C) : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  sConstruction P ⋙ nerveFunctor

def diagonal (P : ObjectProperty C) : SSet.{max u v} where
  obj n := ((bisimplicial P).obj n).obj n
  map {m n} α := ((bisimplicial P).map α).app m ≫ ((bisimplicial P).obj n).map α
  map_id n := by
    ext a
    rfl
  map_comp α β := by simp only [Functor.map_comp]; rw [← NatTrans.naturality]; rfl

variable {D : Type u} [Category.{v} D] [Abelian D]

def mapLevel (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ x, P x → Q (F.obj x)) (n : ℕ) : SLevel P n ⥤ SLevel Q n where
  obj A := ⟨A.obj ⋙ F, by
    refine ⟨fun a => hF _ (A.property.1 a), fun i => F.map_isZero (A.property.2.1 i), ?_⟩
    intro i j k h h'
    obtain ⟨w, hw⟩ := A.property.2.2 i j k h h'
    refine ⟨?_, hw.map_of_exact F⟩
    change F.map (A.obj.map (first h h')) ≫ F.map (A.obj.map (second h h')) = 0
    rw [← Functor.map_comp, w, Functor.map_zero]⟩
  map a := ObjectProperty.homMk (Functor.whiskerRight a.hom F)

def mapDiagonal (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ x, P x → Q (F.obj x)) : diagonal P ⟶ diagonal Q where
  app n := (nerveMap (mapLevel P Q F hF n.unop.len).core).app n
  naturality {X Y} α := by rfl

def zeroFlag (P : ObjectProperty C) (hP : P (0 : C)) (n : ℕ) : SLevel P n :=
  ⟨(Functor.const (Arrow (Fin (n + 1)))).obj (0 : C), by
    refine ⟨fun _ => hP, fun _ => isZero_zero C, ?_⟩
    intro i j k h h'
    refine ⟨by simp, ?_⟩
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C))
      (by infer_instance) (by infer_instance)⟩

def basePoint (P : ObjectProperty C) (hP : P (0 : C)) :
    SSet.toTop.obj (diagonal P) :=
  TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app (diagonal P)).app (op ⦋0⦌)
    (nerveEquiv.symm (Core.mk (zeroFlag P hP 0))))

abbrev HigherGroup (P : ObjectProperty C) (hP : P (0 : C)) (n : ℕ) :=
  HomotopyGroup.Pi (n + 1) (SSet.toTop.obj (diagonal P)) (basePoint P hP)

end MathlibExt.AlgebraicGeometry.WaldhausenExactFlags
