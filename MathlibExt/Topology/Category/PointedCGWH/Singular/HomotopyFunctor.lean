/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
public import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup

/-!
# Every literal degree of the original pointed singular homotopy functor

The carrier is the homotopy type of the actual original singular space at
the original chosen point. Every pointed map gives the original singular
map and its genuine point equation. Identity, composition, the constant
class and both Iso directions are retained in every degree, including all
degree-zero components.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Simplicial
open scoped Simplicial

namespace PointedCGWH.SingularHomotopyGeometry

/-- The entire original CGWH inclusion followed by its actual singular functor. -/
abbrev underlyingSingularFunctor : CGWH.{u, v} ⥤ SSet.{v} :=
  CGWH.cgwhToTop ⋙ TopCat.toSSet

/-- The entire original pointed space is included and then singularized. -/
def singularFunctor : PointedCGWH.{u, v} ⥤ SSet.{v} :=
  Under.forget CGWH.point ⋙ underlyingSingularFunctor

/-- The actual singular vertex of the same original chosen point. -/
def singularPoint (X : PointedCGWH.{u, v}) : (singularFunctor.obj X) _⦋0⦌ :=
  TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv X.right X.hom)

/-- Every actual original pointed map preserves the same singular vertex. -/
theorem singularPoint_naturality {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (singularFunctor.map f).app _ (singularPoint X) = singularPoint Y := by
  change TopCat.toSSetObj₀Equiv.symm (f.right (X.hom PUnit.unit)) =
    TopCat.toSSetObj₀Equiv.symm (Y.hom PUnit.unit)
  exact congrArg TopCat.toSSetObj₀Equiv.symm
    (ConcreteCategory.congr_hom (Under.w f) PUnit.unit)

/-- All original pointed singular homotopy types form a full functor in each literal degree. -/
def piFunctor (n : ℕ) : PointedCGWH.{u, v} ⥤ Type v where
  obj X := SSet.KanComplex.π n (singularFunctor.obj X) (singularPoint X)
  map f := TypeCat.ofHom
    (SSet.KanComplex.π.map (singularFunctor.map f) (singularPoint_naturality f) n)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro q
    exact (congrFun (SSet.KanComplex.π.map_congr
      (singularFunctor.map_id X) _ rfl n) q).trans
      (SSet.KanComplex.π.map_id_apply q)
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext
    intro q
    have hPoint : (singularFunctor.map f ≫ singularFunctor.map g).app _
        (singularPoint X) = singularPoint Z := by
      change (singularFunctor.map g).app _
        ((singularFunctor.map f).app _ (singularPoint X)) = _
      rw [singularPoint_naturality, singularPoint_naturality]
    exact (congrFun (SSet.KanComplex.π.map_congr
      (singularFunctor.map_comp f g) _ hPoint n) q).trans
      (SSet.KanComplex.π.map_comp_apply (singularFunctor.map f) (singularFunctor.map g)
        (singularPoint_naturality f) (singularPoint_naturality g) hPoint q)

/-- The homotopy functor keeps the actual original constant class in every degree. -/
instance piFunctorOne (n : ℕ) (X : PointedCGWH.{u, v}) :
    One ((piFunctor n).obj X) :=
  inferInstanceAs (One (SSet.KanComplex.π n (singularFunctor.obj X) (singularPoint X)))

/-- Every full functor map is the actual original singular homotopy function. -/
theorem piFunctor_map (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (piFunctor n).map f = TypeCat.ofHom
      (SSet.KanComplex.π.map (singularFunctor.map f) (singularPoint_naturality f) n) := rfl

/-- Every original map preserves the exact constant class, including degree zero. -/
theorem piFunctor_map_one (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (piFunctor n).map f (1 : (piFunctor n).obj X) = 1 :=
  SSet.KanComplex.π.map_one (singularFunctor.map f) (singularPoint_naturality f) n

/-- An entire original pointed Iso induces its full singular homotopy equivalence. -/
def piEquivOfPointedIso (n : ℕ) {X Y : PointedCGWH.{u, v}} (e : X ≅ Y) :
    (piFunctor n).obj X ≃ (piFunctor n).obj Y :=
  SSet.KanComplex.π.equivOfIso (singularFunctor.mapIso e)
    (singularPoint_naturality e.hom) n

/-- The forward equivalence is exactly the homotopy map of the original forward Iso. -/
theorem piEquivOfPointedIso_apply (n : ℕ) {X Y : PointedCGWH.{u, v}} (e : X ≅ Y)
    (q : (piFunctor n).obj X) :
    piEquivOfPointedIso n e q = (piFunctor n).map e.hom q := rfl

/-- The inverse equivalence is exactly the homotopy map of the original inverse Iso. -/
theorem piEquivOfPointedIso_symm_apply (n : ℕ) {X Y : PointedCGWH.{u, v}} (e : X ≅ Y)
    (q : (piFunctor n).obj Y) :
    (piEquivOfPointedIso n e).symm q = (piFunctor n).map e.inv q := rfl

/-- The full equivalence preserves the same original constant class. -/
theorem piEquivOfPointedIso_one (n : ℕ) {X Y : PointedCGWH.{u, v}} (e : X ≅ Y) :
    piEquivOfPointedIso n e (1 : (piFunctor n).obj X) = 1 :=
  piFunctor_map_one n e.hom

/-- The actual inverse equivalence preserves the original constant class as well. -/
theorem piEquivOfPointedIso_symm_one (n : ℕ) {X Y : PointedCGWH.{u, v}} (e : X ≅ Y) :
    (piEquivOfPointedIso n e).symm (1 : (piFunctor n).obj Y) = 1 :=
  piFunctor_map_one n e.inv

end PointedCGWH.SingularHomotopyGeometry
