/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.CyclicWorkingHeight
public import MathlibExt.Algebra.Homology.HomologicalComplex.MapColimits

/-!
# Connes cokernels and algebra maps in a common carrier universe

For a nonunital ring A with a k-module structure and k-bilinear multiplication, lift its
cyclic bicomplex degreewise to h = max u v z. The Connes model at this height is the cokernel
of the first horizontal column map, regarded as a nonnegative chain complex.

The exact module ULift functor preserves this cokernel, giving an isomorphism from the lifted
base Connes complex to the cokernel formed at height h. It preserves the quotient projection.
A nonunital k-algebra homomorphism between independently sized algebras gives a map of these
quotients at their common height and induced maps on homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. cyclicBicomplexAtHeight applies U_h in each cell
of cyclicBicomplex k A, using down ℕ in both directions. Its horizontal and vertical maps are
the images of the base bicomplex maps. -/
abbrev cyclicBicomplexAtHeight :=
  (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. connesComplexAtHeight is the cokernel in chain
complexes of (cyclicBicomplexAtHeight k A).d 1 0. It is the first-column Connes quotient in
ModuleCat.{h} k. -/
abbrev connesComplexAtHeight :=
  HomologicalComplex₂.firstColumnCokernel (cyclicBicomplexAtHeight.{u,v,z} k A)

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. Cokernel preservation gives U_h(connesComplex k
A) ≅ connesComplexAtHeight k A. The comparison is PreservesCokernel.iso applied to the first
horizontal map of the base cyclic bicomplex. -/
def connesComplexLiftIsoAtHeight :
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (connesComplex k A) ≅ connesComplexAtHeight.{u,v,z} k A :=
  PreservesCokernel.iso
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ))
    ((cyclicBicomplex k A).d 1 0)

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. Let e be connesComplexLiftIsoAtHeight and π the
cokernel projection of the base first-column map. Then U_h.map π ≫ e.hom equals the cokernel
projection of the lifted first-column map. -/
@[reassoc]
theorem connesComplexLiftIsoAtHeight_π :
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (cokernel.π ((cyclicBicomplex k A).d 1 0)) ≫
      (connesComplexLiftIsoAtHeight.{u,v,z} k A).hom =
        cokernel.π ((cyclicBicomplexAtHeight.{u,v,z} k A).d 1 0) :=
  PreservesCokernel.π_iso_hom
    ((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ))
    ((cyclicBicomplex k A).d 1 0)

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. For n : ℕ, connesProjectionAtHeight n is the
degree-n component of cokernel.π ((cyclicBicomplexAtHeight k A).d 1 0), from column zero to
the Connes complex. -/
def connesProjectionAtHeight (n : ℕ) :=
  (cokernel.π ((cyclicBicomplexAtHeight.{u,v,z} k A).d 1 0)).f n

variable {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. The map connesComplexHomAtHeight f : connesComplexAtHeight A ⟶
connesComplexAtHeight B is the first-column cokernel map induced by cyclicBicomplexMapAtHeight
f. -/
def connesComplexHomAtHeight (f : A →ₙₐ[k] B) :
    connesComplexAtHeight.{u,v,max u v w z} k A ⟶
      connesComplexAtHeight.{u,w,max u v w z} k B :=
  let φ : cyclicBicomplexAtHeight.{u,v,max u v w z} k A ⟶
      cyclicBicomplexAtHeight.{u,w,max u v w z} k B := cyclicBicomplexMapAtHeight.{u,v,w,z} f
  HomologicalComplex₂.firstColumnCokernelMap φ

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. For n : ℕ, π_A,n ≫ connesComplexHomAtHeight(f).f n =
cyclicBicomplexMapAtHeight(f).f 0.f n ≫ π_B,n, where π_A,n and π_B,n are the respective Connes
projections at height H. -/
@[reassoc]
theorem connesProjectionAtHeight_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    connesProjectionAtHeight.{u,v,max u v w z} k A n ≫
        (connesComplexHomAtHeight.{u,v,w,z} k A f).f n =
      ((cyclicBicomplexMapAtHeight.{u,v,w,z} f).f 0).f n ≫
        connesProjectionAtHeight.{u,w,max u v w z} k B n := by
  let φ : cyclicBicomplexAtHeight.{u,v,max u v w z} k A ⟶
      cyclicBicomplexAtHeight.{u,w,max u v w z} k B := cyclicBicomplexMapAtHeight.{u,v,w,z} f
  let E := HomologicalComplex.eval (ModuleCat.{max u v w z} k) (ComplexShape.down ℕ) n
  have h := E.congr_map (HomologicalComplex₂.firstColumnCokernelMap_π φ)
  simpa only [E, φ, Functor.map_comp, HomologicalComplex.eval_map, HomologicalComplex.eval_obj,
    HomologicalComplex.comp_f, connesComplexHomAtHeight, connesProjectionAtHeight,
    connesComplexAtHeight, cyclicBicomplexAtHeight] using h

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
For a spare universe z, put h = max u v z and let U_h be the module ULift functor from max u v
to h, applied degreewise to chain complexes. For n : ℕ, connesHomologyAtHeight n is
(connesComplexAtHeight k A).homology n, the homology object in ModuleCat.{h} k. -/
abbrev connesHomologyAtHeight (n : ℕ) := (connesComplexAtHeight.{u,v,z} k A).homology n

/-- Let k : Type u be a commutative ring and A : Type v a nonunital ring with a k-module structure
and k-bilinear multiplication, as expressed by IsScalarTower k A A and SMulCommClass k A A.
Let B : Type w have the same nonunital k-algebra structure, let f : A →ₙₐ[k] B, and use common
height H = max u v w z. For n : ℕ, connesHomologyMapAtHeight f n is homologyMap
(connesComplexHomAtHeight f) n from the height-H Connes homology of A to that of B. -/
def connesHomologyMapAtHeight (f : A →ₙₐ[k] B) (n : ℕ) :
    connesHomologyAtHeight.{u,v,max u v w z} k A n ⟶
      connesHomologyAtHeight.{u,w,max u v w z} k B n :=
  HomologicalComplex.homologyMap (connesComplexHomAtHeight.{u,v,w,z} k A f) n

end ModuleCat.Algebra.Hochschild.NonUnital
