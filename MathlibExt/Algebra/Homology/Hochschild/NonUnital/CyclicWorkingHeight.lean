/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.UliftComposition
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic

/-!
# Cyclic bicomplex and homology maps at a common height

Let k be commutative and let A and B be nonunital k-algebra rings whose multiplication is
k-bilinear. For f : A →ₙₐ[k] B, the cyclic bicomplex map is lifted to H = max u v w z, using
the canonical isomorphisms that flatten repeated module lifts. In each cell it maps the
coefficient and every tensor factor by f.

Totalization gives a chain map of the lifted cyclic totals. Transporting its homology through
the canonical lift/homology comparisons defines a map between the lifted base cyclic homology
objects. The displayed comparison square characterizes this map and retains all carrier
universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable {k : Type u} [CommRing k] {A : Type v} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. cyclicBicomplexMapAtHeight maps the degreewise lifted cyclic bicomplex
of A to that of B. It is the further lift of cyclicBicomplexMap f, conjugated by the
repeated-lift flattening isomorphisms. -/
def cyclicBicomplexMapAtHeight (f : A →ₙₐ[k] B) :
    (((ModuleCat.uliftFunctor.{max u v w z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicBicomplex k A) ⟶
    (((ModuleCat.uliftFunctor.{max u v w z, max u w} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicBicomplex k B) := by
  let U := ModuleCat.uliftFunctor.{max u v w z, max u v w} k
  let eA := ModuleCat.uliftFunctorCompIso.{w,max u v w z,max u v,u} k
  let eB := ModuleCat.uliftFunctorCompIso.{v,max u v w z,max u w,u} k
  let eA₁ := Functor.mapHomologicalComplexCompIso eA (ComplexShape.down ℕ)
  let eB₁ := Functor.mapHomologicalComplexCompIso eB (ComplexShape.down ℕ)
  let eA₂ := Functor.mapHomologicalComplexCompIso eA₁ (ComplexShape.down ℕ)
  let eB₂ := Functor.mapHomologicalComplexCompIso eB₁ (ComplexShape.down ℕ)
  exact eA₂.inv.app (cyclicBicomplex k A) ≫
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (cyclicBicomplexMap f) ≫ eB₂.hom.app (cyclicBicomplex k B)

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. For p, q : ℕ and x : A ⊗[k] TensorPower k q A, the cell (p,q) map
sends ULift.up x to ULift.up (TensorPower.consLevelMap f q x). Thus f acts on the
distinguished coefficient and each of the q tensor factors. -/
theorem cyclicBicomplexMapAtHeight_f_f_up (f : A →ₙₐ[k] B) (p q : ℕ)
    (x : chainLevel k A A q) :
    (((cyclicBicomplexMapAtHeight.{u,v,w,z} f).f p).f q).hom (ULift.up x) =
      ULift.up (TensorPower.consLevelMap (f : A →ₗ[k] B) q x) := by
  change ULift.up (((((cyclicBicomplexMap f).f p).f q).hom (ULift.up x)).down) =
    ULift.up (TensorPower.consLevelMap (f : A →ₗ[k] B) q x)
  have h := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (cyclicBicomplexMap_f_f f p q)) (ULift.up x)
  have hv := h.trans (levelMapLift_apply (f : A →ₗ[k] B) q (ULift.up x))
  exact congrArg ULift.up (congrArg ULift.down hv)

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. cyclicTotalMapAtHeight f is HomologicalComplex₂.total.map of
cyclicBicomplexMapAtHeight f, with total shape down ℕ. -/
def cyclicTotalMapAtHeight (f : A →ₙₐ[k] B) :=
  HomologicalComplex₂.total.map (cyclicBicomplexMapAtHeight.{u,v,w,z} f) (ComplexShape.down ℕ)

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. For n : ℕ, cyclicHomologyMapAtHeight maps U_H(HC_n(A)) to
U_H(HC_n(B)). If e_A and e_B are the lift-to-total-homology isomorphisms, it is e_A.hom ≫
H_n(cyclicTotalMapAtHeight f) ≫ e_B.inv. -/
def cyclicHomologyMapAtHeight (f : A →ₙₐ[k] B) (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v w z, max u v} k).obj (cyclicHomology k A n) ⟶
      (ModuleCat.uliftFunctor.{max u v w z, max u w} k).obj (cyclicHomology k B n) :=
  (cyclicHomologyLiftIso.{max u v w z} k A n).hom ≫
    HomologicalComplex.homologyMap (cyclicTotalMapAtHeight.{u,v,w,z} f) n ≫
      (cyclicHomologyLiftIso.{max u v w z} k B n).inv

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. For n : ℕ and lift comparisons e_A, e_B, cyclicHomologyMapAtHeight f n
≫ e_B.hom = e_A.hom ≫ homologyMap (cyclicTotalMapAtHeight f) n. Both sides map the lifted base
homology of A to the homology of B's lifted total. -/
theorem cyclicHomologyMapAtHeight_lift (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMapAtHeight.{u,v,w,z} f n ≫ (cyclicHomologyLiftIso.{max u v w z} k B n).hom =
      (cyclicHomologyLiftIso.{max u v w z} k A n).hom ≫
        HomologicalComplex.homologyMap (cyclicTotalMapAtHeight.{u,v,w,z} f) n := by
  let eA := cyclicHomologyLiftIso.{max u v w z} k A n
  let eB := cyclicHomologyLiftIso.{max u v w z} k B n
  let m := HomologicalComplex.homologyMap (cyclicTotalMapAtHeight.{u,v,w,z} f) n
  have h : (m ≫ eB.inv) ≫ eB.hom = m :=
    (Category.assoc m eB.inv eB.hom).trans
      ((congrArg (fun q => m ≫ q) eB.inv_hom_id).trans (Category.comp_id m))
  exact (Category.assoc eA.hom (m ≫ eB.inv) eB.hom).trans (congrArg (fun q => eA.hom ≫ q) h)

end ModuleCat.Algebra.Hochschild.NonUnital
