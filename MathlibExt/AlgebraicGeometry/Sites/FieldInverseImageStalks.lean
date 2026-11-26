/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricClosureComparison
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageGerms
public import MathlibExt.FieldTheory.Galois.UnitsContinuousModule
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricStalkGaloisAction
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Equivariant stalk change under compatible field embeddings

Let k, Ω, K, Ψ be fields in universe u with separable closures Ω/k and Ψ/K.
A compatible field map consists of β : k → K and σ : Ω → Ψ satisfying
σ ∘ algebraMap(k, Ω) = algebraMap(K, Ψ) ∘ β.
It gives f = Spec β : Spec K → Spec k and a continuous restriction
res_e : Gal(Ψ/K) → Gal(Ω/k).

For abelian sheaves Q with coefficients in c = max(u, w), the stalk
comparison is the natural equivariant isomorphism
Res_(res_e)(Q_Ω) ≅ (f*Q)_Ψ.
On the germ of a ∈ Q(U) at z : Spec Ω → U, it applies the inverse-image
unit to a and takes the germ at the pullback lift of z ∘ Spec σ
over Spec Ψ. The module also describes the point, fiber and underlying
stalk comparisons, and their compatibility with spectrum automorphisms.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace GaloisUnits.FieldMap

variable {k Ω K Ψ : Type u} [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ]

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
The induced k-algebra structure on Ψ has algebra map
k → Ψ equal to algebraMap(K, Ψ) ∘ β.
This construction only uses the compatible field square. -/
@[instance_reducible]
def sourceBaseAlgebra (e : FieldMap k Ω K Ψ) : Algebra k Ψ :=
  ((algebraMap K Ψ).comp e.base).toAlgebra

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
For that induced k-algebra structure on Ψ, the extension map σ
is the k-algebra homomorphism Ω →ₐ[k] Ψ.
Its scalar compatibility is precisely the commuting field square. -/
def extensionAlgHom (e : FieldMap k Ω K Ψ) :
    letI : Algebra k Ψ := sourceBaseAlgebra e
    Ω →ₐ[k] Ψ := by
  letI : Algebra k Ψ := sourceBaseAlgebra e
  exact { e.extension with commutes' := fun x => e.comm_apply x }

@[simp] theorem extensionAlgHom_apply (e : FieldMap k Ω K Ψ) (x : Ω) :
    extensionAlgHom e x = e.extension x := rfl

end GaloisUnits.FieldMap

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]
attribute [local instance] IsSepClosure.sep_closed

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
The base embedding β gives f = Spec β : Spec K → Spec k,
the scheme morphism used by the inverse-image functor. -/
def fieldOriginalPullback (e : GaloisUnits.FieldMap k Ω K Ψ) :
    Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom e.base)

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldOriginalImagePoint (e : GaloisUnits.FieldMap k Ω K Ψ) :
    let : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
    Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e = Spec.algebraMap k Ψ := by
  let : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
  rw [fieldOriginalPullback, ← Spec.map_comp]
  rfl


/-- Let X, Z be schemes in universe u, x, y : Z → X equal
morphisms, and U an object over X. An over-X morphism
(Z, x) → U transports to (Z, y) → U along x = y, with the
same underlying scheme map Z → U. -/
def overHomSourceChange {X Z : Scheme.{u}} (x y : Z ⟶ X) (h : x = y)
    (U : Over X) (z : Over.mk x ⟶ U) : Over.mk y ⟶ U :=
  Over.homMk z.left (z.w.trans h)

/-- Let X, Z, Z′ be schemes, x : Z → X and y = y′ : Z′ → X,
and U an object over X. Suppose a : (Z′, y) → (Z, x) and
b : (Z′, y′) → (Z, x) have the same underlying map Z′ → Z.
If precomposition by a maps Hom_X((Z, x), U) surjectively onto
Hom_X((Z′, y), U), then precomposition by b is also surjective. -/
theorem overPrecomp_surjective_source_transport {X Z Z' : Scheme.{u}}
    (x : Z ⟶ X) (y y' : Z' ⟶ X) (h : y = y') (U : Over X)
    (a : Over.mk y ⟶ Over.mk x) (b : Over.mk y' ⟶ Over.mk x)
    (hab : a.left = b.left)
    (ha : Function.Surjective (fun t : Over.mk x ⟶ U => a ≫ t)) :
    Function.Surjective (fun t : Over.mk x ⟶ U => b ≫ t) := by
  subst y'
  have hh : a = b := Over.OverMorphism.ext hab
  exact hh ▸ ha

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
The extension embedding σ gives Spec σ : Spec Ψ → Spec Ω.
Its composite with Spec Ω → Spec k equals
Spec Ψ → Spec K followed by Spec β. -/
def fieldChangeSpec (e : GaloisUnits.FieldMap k Ω K Ψ) : Spec (.of Ψ) ⟶ Spec (.of Ω) :=
  Spec.map (CommRingCat.ofHom e.extension)

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldChangeSpec_source_square (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldChangeSpec k Ω K Ψ e ≫ Spec.algebraMap k Ω =
      Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e := by
  change Spec.map (CommRingCat.ofHom e.extension) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
    Spec.map (CommRingCat.ofHom (algebraMap K Ψ)) ≫ Spec.map (CommRingCat.ofHom e.base)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext t
  exact e.comm_apply t

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldChangeSpec_eq (e : GaloisUnits.FieldMap k Ω K Ψ) :
    let : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
    fieldChangeSpec k Ω K Ψ e =
      fieldClosureSpec k Ω Ψ (GaloisUnits.FieldMap.extensionAlgHom e) := rfl

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Spec σ is a morphism over Spec k from the image of the Ψ-valued
point along f to the Ω-valued point, because the two maps from
Spec Ψ to Spec k agree. -/
def fieldChangeOverHom (e : GaloisUnits.FieldMap k Ω K Ψ) :
    Over.mk (Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e) ⟶
      Over.mk (Spec.algebraMap k Ω) :=
  Over.homMk (fieldChangeSpec k Ω K Ψ e) (fieldChangeSpec_source_square k Ω K Ψ e)

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
The induced point morphism goes from the Ψ-valued image point over
Spec k to the Ω-valued point. Its fiber map sends a geometric lift
z : Spec Ω → U to z ∘ Spec σ. -/
def fieldChangeImagePointHom (e : GaloisUnits.FieldMap k Ω K Ψ) :
    Scheme.pointSmallEtale (Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e) ⟶
      fieldGeometricPoint k Ω :=
  ⟨Functor.whiskerLeft (Scheme.Etale.forget (Spec (.of k)))
    (coyoneda.map (fieldChangeOverHom k Ω K Ψ e).op)⟩

theorem fieldChangeImagePointHom_app_left (e : GaloisUnits.FieldMap k Ω K Ψ)
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (((fieldChangeImagePointHom k Ω K Ψ e).hom.app U) z).left =
      fieldChangeSpec k Ω K Ψ e ≫ z.left := rfl

set_option backward.isDefEq.respectTransparency false in
-- The same original Etale/Over aliases were recorded in PointComparisonV1.
theorem fieldChangeImagePointHom_app_injective (e : GaloisUnits.FieldMap k Ω K Ψ)
    (U : (Spec (.of k)).Etale) :
    Function.Injective ((fieldChangeImagePointHom k Ω K Ψ e).hom.app U) := by
  let : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
  let σ := GaloisUnits.FieldMap.extensionAlgHom e
  let : Epi (fieldChangeSpec k Ω K Ψ e) := fieldClosureSpec_epi k Ω Ψ σ
  intro z z' h
  apply Over.OverMorphism.ext
  have hh := congrArg Over.Hom.left h
  have hs : fieldChangeSpec k Ω K Ψ e ≫ z.left = fieldChangeSpec k Ω K Ψ e ≫ z'.left :=
    (fieldChangeImagePointHom_app_left k Ω K Ψ e U z).symm.trans
      (hh.trans (fieldChangeImagePointHom_app_left k Ω K Ψ e U z'))
  exact (cancel_epi (fieldChangeSpec k Ω K Ψ e)).mp hs

set_option backward.isDefEq.respectTransparency false in
-- No affine or finite-component restriction: reuse the proved original full-U comparison.
theorem fieldChangeImagePointHom_app_surjective (e : GaloisUnits.FieldMap k Ω K Ψ)
    (U : (Spec (.of k)).Etale) :
    Function.Surjective ((fieldChangeImagePointHom k Ω K Ψ e).hom.app U) := by
  let : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
  let σ := GaloisUnits.FieldMap.extensionAlgHom e
  let V := (Scheme.Etale.forget (Spec (.of k))).obj U
  let a := fieldClosureOverHom k Ω Ψ σ
  let b := fieldChangeOverHom k Ω K Ψ e
  have ha : Function.Surjective
      (fun t : Over.mk (Spec.algebraMap k Ω) ⟶ V => a ≫ t) :=
    fieldClosurePointHom_app_surjective k Ω Ψ σ U
  have hab : a.left = b.left := (fieldChangeSpec_eq k Ω K Ψ e).symm
  exact overPrecomp_surjective_source_transport
    (Spec.algebraMap k Ω) (Spec.algebraMap k Ψ)
    (Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e)
    (fieldOriginalImagePoint k Ω K Ψ e).symm V a b hab ha

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
Precomposition with Spec σ is a natural isomorphism from the
Ω-valued fiber functor on Etale(Spec k) to the Ψ-valued image-point
fiber functor, with value z ↦ z ∘ Spec σ. -/
def fieldChangeImageFiberIso (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (fieldGeometricPoint k Ω).fiber ≅
      (Scheme.pointSmallEtale (Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e)).fiber :=
  NatIso.ofComponents (fun U => (Equiv.ofBijective
    ((fieldChangeImagePointHom k Ω K Ψ e).hom.app U)
    ⟨fieldChangeImagePointHom_app_injective k Ω K Ψ e U,
      fieldChangeImagePointHom_app_surjective k Ω K Ψ e U⟩).toIso)
    (fun f => (fieldChangeImagePointHom k Ω K Ψ e).hom.naturality f)

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
This is the isomorphism from the Ψ-valued image point over Spec k
to the Ω-valued point. Its fiber map is precomposition by Spec σ;
its inverse uses the bijective fiber maps. -/
def fieldChangeImagePointIso (e : GaloisUnits.FieldMap k Ω K Ψ) :
    Scheme.pointSmallEtale (Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e) ≅
      fieldGeometricPoint k Ω where
  hom := fieldChangeImagePointHom k Ω K Ψ e
  inv := ⟨(fieldChangeImageFiberIso k Ω K Ψ e).inv⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (fieldChangeImageFiberIso k Ω K Ψ e).inv_hom_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (fieldChangeImageFiberIso k Ω K Ψ e).hom_inv_id

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
The image-point isomorphism holds for common-universe points
whose fiber coordinates are lifted to c. It uses the same embedding
and the same underlying geometric lifts. -/
def fieldChangeCommonImagePointIso (e : GaloisUnits.FieldMap k Ω K Ψ) :
    smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e) ≅
      smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω) where
  hom := ⟨Functor.whiskerRight (fieldChangeImagePointHom k Ω K Ψ e).hom uliftFunctor.{w, u}⟩
  inv := ⟨(Functor.isoWhiskerRight (fieldChangeImageFiberIso k Ω K Ψ e) uliftFunctor.{w, u}).inv⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (Functor.isoWhiskerRight (fieldChangeImageFiberIso k Ω K Ψ e) uliftFunctor.{w, u}).inv_hom_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (Functor.isoWhiskerRight (fieldChangeImageFiberIso k Ω K Ψ e) uliftFunctor.{w, u}).hom_inv_id

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
The point isomorphism gives the natural additive stalk isomorphism
Q_Ω ≅ Q_(Ψ over k) on coefficient sheaves over Spec k.
Its direction is from the source closure stalk to the image-point stalk. -/
def fieldChangeImageStalkIso (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
        (A := AddCommGrpCat.{max u w}) ≅
      (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e)).sheafFiber
        (A := AddCommGrpCat.{max u w}) where
  hom := (fieldChangeCommonImagePointIso.{u, w} k Ω K Ψ e).hom.sheafFiber
  inv := (fieldChangeCommonImagePointIso.{u, w} k Ω K Ψ e).inv.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (fieldChangeCommonImagePointIso.{u, w} k Ω K Ψ e).inv_hom_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (fieldChangeCommonImagePointIso.{u, w} k Ω K Ψ e).hom_inv_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
Closure change and the inverse-image stalk comparison give
Q_Ω ≅ (f*Q)_Ψ, naturally in the coefficient sheaf Q. -/
def fieldChangeUnderlyingStalkIso (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
        (A := AddCommGrpCat.{max u w}) ≅
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).sheafFiber
          (A := AddCommGrpCat.{max u w}) :=
  fieldChangeImageStalkIso.{u, w} k Ω K Ψ e ≪≫
    (smallEtaleInverseImageCommonGeometricStalkIso.{u, w}
      (fieldOriginalPullback k Ω K Ψ e) (Spec.algebraMap K Ψ)).symm

/-- Let h : X → Y be a scheme morphism in universe u, Λ a separably
closed field in universe u, x : Spec Λ → X, and U ∈ Etale(Y).
The inverse common-universe fiber comparison sends ULift.up(z) to
ULift.up of the inverse ordinary fiber comparison applied to z.
Both compare lifts of h ∘ x to U with lifts of x to U ×_Y X. -/
theorem smallEtaleBaseChangeCommonPointFiberIso_inv_up
    {Λ : Type u} [Field Λ] [IsSepClosed Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Λ) ⟶ X) (U : Y.Etale)
    (z : (Scheme.pointSmallEtale (x ≫ f)).fiber.obj U) :
    (smallEtaleBaseChangeCommonPointFiberIso.{u, w} f x).inv.app U (ULift.up z) =
      ULift.up ((smallEtaleBaseChangePointFiberIso f x).inv.app U z) := rfl

/-- Let h : X → Y be a scheme morphism, Λ a separably closed field,
x : Spec Λ → X, and z a geometric lift of h ∘ x to U ∈ Etale(Y).
The inverse fiber comparison produces a lift to U ×_Y X whose
projection to U is z. -/
theorem smallEtaleBaseChangePointFiberIso_inv_app_fst
    {Λ : Type u} [Field Λ] [IsSepClosed Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Λ) ⟶ X) (U : Y.Etale)
    (z : (Scheme.pointSmallEtale (x ≫ f)).fiber.obj U) :
    ((smallEtaleBaseChangePointFiberIso f x).inv.app U z).left ≫ pullback.fst U.hom f = z.left := by
  let β := smallEtaleBaseChangePointFiberIso f x
  have hβ : β.hom.app U (β.inv.app U z) = z := by
    simpa only [types_comp_apply, types_id_apply] using types_congr_hom (β.inv_hom_id_app U) z
  have hp := smallEtaleBaseChangePointFiberIso_hom_app_left f x U (β.inv.app U z)
  exact hp.symm.trans (congrArg Over.Hom.left hβ)

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
For U ∈ Etale(Spec k) and z : Spec Ω → U over k, this is the
Ψ-valued lift to U ×_(Spec k) Spec K obtained by inverse base change
from z ∘ Spec σ. It is independent of coefficient sheaves. -/
def fieldChangeOriginalPoint (e : GaloisUnits.FieldMap k Ω K Ψ)
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (fieldGeometricPoint K Ψ).fiber.obj
      ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U) :=
  ((smallEtaleBaseChangePointFiberIso
    (fieldOriginalPullback k Ω K Ψ e) (Spec.algebraMap K Ψ)).inv.app U)
    (((fieldChangeImagePointHom k Ω K Ψ e).hom.app U) z)

theorem fieldChangeOriginalPoint_snd (e : GaloisUnits.FieldMap k Ω K Ψ)
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (fieldChangeOriginalPoint k Ω K Ψ e U z).left ≫
        pullback.snd U.hom (fieldOriginalPullback k Ω K Ψ e) = Spec.algebraMap K Ψ :=
  (fieldChangeOriginalPoint k Ω K Ψ e U z).w

set_option backward.isDefEq.respectTransparency false in
-- Use the raw inverse identity and raw projection; no field-image functor casts.
theorem fieldChangeOriginalPoint_fst (e : GaloisUnits.FieldMap k Ω K Ψ)
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (fieldChangeOriginalPoint k Ω K Ψ e U z).left ≫
        pullback.fst U.hom (fieldOriginalPullback k Ω K Ψ e) =
      fieldChangeSpec k Ω K Ψ e ≫ z.left := by
  exact (smallEtaleBaseChangePointFiberIso_inv_app_fst
    (fieldOriginalPullback k Ω K Ψ e) (Spec.algebraMap K Ψ) U
    (((fieldChangeImagePointHom k Ω K Ψ e).hom.app U) z)).trans
      (fieldChangeImagePointHom_app_left k Ω K Ψ e U z)

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
For a coefficient sheaf Q, U ∈ Etale(Spec k), z ∈ U(Ω), and
a ∈ Q(U), the image-stalk isomorphism sends germ_(U,z)(a)
to germ_(U,z∘Spec σ)(a) at the Ψ-valued image point over k. -/
theorem fieldChangeImageStalkIso_original_germ (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj ≫ (fieldChangeImageStalkIso.{u, w} k Ω K Ψ e).hom.app Q =
      (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap K Ψ ≫ fieldOriginalPullback k Ω K Ψ e)).toPresheafFiber
        U (ULift.up (((fieldChangeImagePointHom k Ω K Ψ e).hom.app U) z)) Q.obj := by
  change _ ≫ (smallEtaleGeometricPointCommon.{u, w}
    (Spec.algebraMap k Ω)).presheafFiberDesc (A := AddCommGrpCat.{max u w}) (P := Q.obj) _ _ = _
  exact (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber_presheafFiberDesc
    (A := AddCommGrpCat.{max u w}) (P := Q.obj) _ _ U (ULift.up z)

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
The underlying inverse-image stalk comparison sends a germ (U, z, a)
to the Ψ-germ of η_Q,U(a) over U ×_(Spec k) Spec K at the changed
lift z_e. Here η : Q → f_*f*Q is the inverse-image adjunction unit. -/
theorem fieldChangeUnderlyingStalkIso_original_germ (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj ≫ (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q =
      ((smallEtaleInverseImageAdjunction.{u, w} (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app
          (op U) ≫
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
          ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U)
          (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U z))
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj := by
  let f := fieldOriginalPullback k Ω K Ψ e
  let χ := fieldChangeImageStalkIso.{u, w} k Ω K Ψ e
  let κ := smallEtaleInverseImageCommonGeometricStalkIso.{u, w} f (Spec.algebraMap K Ψ)
  have hχ := fieldChangeImageStalkIso_original_germ.{u, w} k Ω K Ψ e Q U z
  have hκ := smallEtaleInverseImageCommonGeometricStalkIso_inv_original_germ.{u, w}
    f (Spec.algebraMap K Ψ) Q U
    (ULift.up (((fieldChangeImagePointHom k Ω K Ψ e).hom.app U) z))
  have hi := smallEtaleBaseChangeCommonPointFiberIso_inv_up.{u, w}
    f (Spec.algebraMap K Ψ) U (((fieldChangeImagePointHom k Ω K Ψ e).hom.app U) z)
  have hg := hκ.trans (congrArg (fun a =>
    ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app (op U) ≫
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
        ((smallEtaleBaseChange f).obj U) a ((smallEtaleInverseImage.{u, w} f).obj Q).obj) hi)
  change _ ≫ (χ.hom.app Q ≫ κ.inv.app Q) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ κ.inv.app Q) hχ).trans hg)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Let h : X → Y be a scheme morphism, Λ a separably closed field,
x : Spec Λ → X, and U ∈ Etale(Y). On a lift z of h ∘ x to U,
the inverse fiber comparison is the pullback adjunction's Hom map
Hom_Y((Spec Λ, h∘x), U) → Hom_X((Spec Λ, x), h*U). -/
theorem smallEtaleBaseChangePointFiberIso_inv_app_overHomEquiv
    {Λ : Type u} [Field Λ] [IsSepClosed Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Spec (.of Λ) ⟶ X) (U : Y.Etale)
    (z : (Scheme.pointSmallEtale (x ≫ f)).fiber.obj U) :
    (smallEtaleBaseChangePointFiberIso f x).inv.app U z =
      (Over.mapPullbackAdj f).homEquiv (Over.mk x) ((Scheme.Etale.forget Y).obj U) z := rfl

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]
attribute [local instance] IsSepClosure.sep_closed

omit [IsSepClosure K Ψ] in
/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
For h ∈ Gal(Ψ/K), the Galois spectrum automorphisms satisfy
Spec σ ∘ γ_h = γ_(res_e h) ∘ Spec σ.
This is the Galois square used by the equivariant stalk comparison. -/
theorem fieldChangeSpec_galois_square (e : GaloisUnits.FieldMap k Ω K Ψ) (h : Gal(Ψ/K)) :
    fieldGaloisSpec K Ψ h ≫ fieldChangeSpec k Ω K Ψ e =
      fieldChangeSpec k Ω K Ψ e ≫ fieldGaloisSpec k Ω (GaloisUnits.FieldMap.restrictHom e h) := by
  change Spec.map (CommRingCat.ofHom h.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.extension) =
    Spec.map (CommRingCat.ofHom e.extension) ≫
      Spec.map (CommRingCat.ofHom (GaloisUnits.FieldMap.restrictHom e h).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext t
  exact (GaloisUnits.FieldMap.restrictHom_comm e h t).symm

omit [IsSepClosure K Ψ] in
set_option backward.isDefEq.respectTransparency false in
-- The actual original Over and Etale aliases require the recorded transparency.
theorem fieldChangeOverHom_galois_comm (e : GaloisUnits.FieldMap k Ω K Ψ) (h : Gal(Ψ/K)) :
    fieldChangeOverHom k Ω K Ψ e ≫
        fieldGaloisOver k Ω (GaloisUnits.FieldMap.restrictHom e h) =
      (Over.map (fieldOriginalPullback k Ω K Ψ e)).map (fieldGaloisOver K Ψ h) ≫
        fieldChangeOverHom k Ω K Ψ e := by
  apply Over.OverMorphism.ext
  exact (fieldChangeSpec_galois_square k Ω K Ψ e h).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- Native β and its genuine homEquiv naturality retain the original point maps.
theorem fieldChangeOriginalPoint_equivariant (e : GaloisUnits.FieldMap k Ω K Ψ)
    (h : Gal(Ψ/K)) (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    fieldChangeOriginalPoint k Ω K Ψ e U
        (fieldGaloisOver k Ω (GaloisUnits.FieldMap.restrictHom e h) ≫ z) =
      fieldGaloisOver K Ψ h ≫ fieldChangeOriginalPoint k Ω K Ψ e U z := by
  let f := fieldOriginalPullback k Ω K Ψ e
  let g := fieldGaloisOver K Ψ h
  let a := fieldChangeOverHom k Ω K Ψ e
  change (Over.mapPullbackAdj f).homEquiv (Over.mk (Spec.algebraMap K Ψ))
      ((Scheme.Etale.forget (Spec (.of k))).obj U)
        (a ≫ (fieldGaloisOver k Ω (GaloisUnits.FieldMap.restrictHom e h) ≫ z)) =
    g ≫ (Over.mapPullbackAdj f).homEquiv (Over.mk (Spec.algebraMap K Ψ))
      ((Scheme.Etale.forget (Spec (.of k))).obj U) (a ≫ z)
  rw [← Category.assoc, fieldChangeOverHom_galois_comm, Category.assoc]
  exact (Over.mapPullbackAdj f).homEquiv_naturality_left g (a ≫ z)

theorem fieldChangeUnderlyingStalkIso_original_germ_apply
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)) :
    (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          U (ULift.up z) Q.obj c) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
        ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U)
        (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U z))
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj
        (((smallEtaleInverseImageAdjunction.{u, w}
          (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op U) c) :=
  ConcreteCategory.congr_hom
    (fieldChangeUnderlyingStalkIso_original_germ.{u, w} k Ω K Ψ e Q U z) c

set_option backward.isDefEq.respectTransparency false in
-- Earlier probes recorded the same original/common stalk and action aliases.
theorem fieldChangeUnderlyingStalkIso_equivariant
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (h : Gal(Ψ/K)) (m : fieldGeometricStalkCarrier.{u, w} k Ω Q) :
    (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
        ((GaloisUnits.FieldMap.restrictHom e h) • m) =
      h • (show fieldGeometricStalkCarrier.{u, w} K Ψ
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) from
        (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q m) := by
  obtain ⟨U, z, c, hc⟩ :=
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber_jointly_surjective m
  rcases z with ⟨z⟩
  subst m
  let f := fieldOriginalPullback k Ω K Ψ e
  let F := (smallEtaleInverseImage.{u, w} f).obj Q
  let α := (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)
  let V := (smallEtaleBaseChange f).obj U
  let ηc := ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app (op U) c
  let zT := fieldChangeOriginalPoint k Ω K Ψ e U z
  have hs := fieldGeometricStalk_smul_germ.{u, w} k Ω Q
    (GaloisUnits.FieldMap.restrictHom e h) U z c
  have hg := fieldChangeUnderlyingStalkIso_original_germ_apply.{u, w} k Ω K Ψ e Q U
    (fieldGaloisOver k Ω (GaloisUnits.FieldMap.restrictHom e h) ≫ z) c
  have hp := fieldChangeOriginalPoint_equivariant k Ω K Ψ e h U z
  have ht := fieldGeometricStalk_smul_germ.{u, w} K Ψ F h V zT ηc
  have h0 := fieldChangeUnderlyingStalkIso_original_germ_apply.{u, w} k Ω K Ψ e Q U z c
  calc
    _ = α ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up (fieldGaloisOver k Ω (GaloisUnits.FieldMap.restrictHom e h) ≫ z)) Q.obj c) :=
      congrArg (fun t => α t) hs
    _ = Φ.toPresheafFiber V
        (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U
          (fieldGaloisOver k Ω (GaloisUnits.FieldMap.restrictHom e h) ≫ z))) F.obj ηc := hg
    _ = Φ.toPresheafFiber V (ULift.up (fieldGaloisOver K Ψ h ≫ zT)) F.obj ηc :=
      congrArg (fun p => Φ.toPresheafFiber V (ULift.up p) F.obj ηc) hp
    _ = h • (show fieldGeometricStalkCarrier.{u, w} K Ψ F from
      Φ.toPresheafFiber V (ULift.up zT) F.obj ηc) := ht.symm
    _ = h • (show fieldGeometricStalkCarrier.{u, w} K Ψ F from
      α ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c)) :=
      congrArg (fun t : fieldGeometricStalkCarrier.{u, w} K Ψ F => h • t) h0.symm

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
For a coefficient sheaf Q, the additive map Q_Ω → (f*Q)_Ψ
is a morphism from the source Galois module restricted along res_e
to the target stalk module in the discrete continuous Gal(Ψ/K)-module
category. -/
def fieldChangeStalkModuleHom (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (GaloisUnits.restrictModules (GaloisUnits.FieldMap.restrictContinuous e)).obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ⟶
      (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) :=
  DiscreteAbelianAction.ofAddHom
    ⟨((fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q).hom,
      fieldChangeUnderlyingStalkIso_equivariant.{u, w} k Ω K Ψ e Q⟩

/-- Let k, Ω, K, Ψ be fields in universe u, with k-algebra Ω
and K-algebra Ψ. Let e consist of embeddings β : k → K and
σ : Ω → Ψ satisfying σ ∘ algebraMap(k, Ω) =
algebraMap(K, Ψ) ∘ β.
Assume Ω/k and Ψ/K are separable closures. Put c = max(u, w)
and f = Spec(β) : Spec K → Spec k.
These maps form the natural isomorphism
Res_(res_e) ∘ E_(k,Ω) ≅ E_(K,Ψ) ∘ f*,
where E denotes the geometric-stalk Galois functor.
The coefficient universe w is independent of the field universe u. -/
def fieldChangeStalkModuleIso (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        GaloisUnits.restrictModules (GaloisUnits.FieldMap.restrictContinuous e) ≅
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} K Ψ :=
  NatIso.ofComponents
    (fun Q => DiscreteAbelianAction.isoOfBijective (fieldChangeStalkModuleHom.{u, w} k Ω K Ψ e Q)
      (by
        change Function.Bijective ((fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q)
        exact ConcreteCategory.bijective_of_isIso _))
    (by
      intro Q Q' τ
      apply (DiscreteAbelianAction.forget Gal(Ψ/K)).map_injective
      change (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map τ ≫
          (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q' =
        (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q ≫
          (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap K Ψ)).map
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map τ)
      exact (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.naturality τ)

theorem fieldChangeStalkModuleIso_hom_underlying
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (DiscreteAbelianAction.forget Gal(Ψ/K)).map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) =
      (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q := rfl

end AlgebraicGeometry.Scheme.DerivedSections

end
