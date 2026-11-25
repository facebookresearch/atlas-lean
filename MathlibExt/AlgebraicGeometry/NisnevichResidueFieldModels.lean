/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original Apache 2.0 license and author credit are retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicGeometry/ResidueField.lean
Module and namespace paths are adapted for Atlas. The Lean 4.35 proof call to
evaluation_eq_zero_iff_notMem_basicOpen adds the explicit argument (U := ⊤).
Source license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import MathlibExt.AlgebraicGeometry.NisnevichResidueDegreeModels

/-!
# Residue fields of schemes and their behaviour under base change

This file records how the condition `(N : κ(x)) ≠ 0`, that a natural number `N` is invertible in
the residue field at a point `x`, carries over between schemes. It is the form in which "`N` is
invertible on the base" enters the theory of level structures on elliptic curves.

It also provides the geometric point `Spec κ(x)ᵃˡᵍ ⟶ X` over a point `x`, through which such
conditions are checked after base change to an algebraically closed field, and computes the
canonical morphism `Spec κ(x) ⟶ X` on the opens containing `x`.

## Main definitions

* `AlgebraicGeometry.Scheme.fromSpecAlgebraicClosure X x`: the morphism `Spec κ(x)ᵃˡᵍ ⟶ X` from
  the spectrum of an algebraic closure of the residue field at `x`, whose image is `{x}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.natCast_residueField_ne_zero`: if `N` is invertible in the residue
  field at `f x`, then it is invertible in the residue field at `x`, for any morphism `f`.
* `AlgebraicGeometry.Spec.natCast_residueField_ne_zero`: if `N` is invertible in a field `K`, then
  it is invertible in the residue field of `Spec K`.
* `AlgebraicGeometry.Scheme.eq_of_SpecMap_comp_fromSpecResidueField`: maps out of `κ(x)` are
  determined by their spectra composed with `Spec κ(x) ⟶ X`, since this morphism is a monomorphism.
* `AlgebraicGeometry.Scheme.fromSpecResidueField_closedPoint_mem`: the closed point of
  `Spec κ(x)` lies over every open containing `x`.
* `AlgebraicGeometry.Scheme.fromSpecResidueField_preimage_eq_top`: the inverse image of an open
  containing `x` under `Spec κ(x) ⟶ X` is everything.
* `AlgebraicGeometry.Scheme.fromSpecResidueField_appLE`: on an open containing `x`, the morphism
  `Spec κ(x) ⟶ X` sends a function to its value at `x`.
* `AlgebraicGeometry.Scheme.residueFieldSectionsIso`: for an open `V` containing `x`, the functions
  on the inverse image of `V` in `Spec κ(x)` are `κ(x)`, and `Spec κ(x) ⟶ X` acts on sections over
  `V` by evaluation at `x` (`Scheme.fromSpecResidueField_app_residueFieldSectionsIso_hom`).
* `RingHom.isIso_SpecMap_residueFieldMap_iff`: for a ring map `φ : R →+* S` and a prime
  `x` of `S`, the residue field map of `Spec S ⟶ Spec R` at `x` is an isomorphism iff the map of
  residue fields `κ(φ⁻¹ x) → κ(x)` is bijective. This translates conditions on residue fields
  between schemes and rings, for instance for étale neighbourhoods built from algebras.
* `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_lift`: a lift along `f` of a morphism
  `Spec A ⟶ X` from a local ring, inducing an isomorphism of residue fields, sends the closed point
  to a preimage of `x` at which `f` induces an isomorphism of residue fields.
* `AlgebraicGeometry.Scheme.residueField_hom_ext`: on a quasi-affine scheme, a ring map out of the
  residue field `κ(x)` is determined by its values on global functions evaluated at `x`.
* `AlgebraicGeometry.Scheme.toSpecΓ_apply_asIdeal`: the point of `Spec Γ(X, ⊤)` under `x` is the
  prime ideal of global functions vanishing at `x`.
* `AlgebraicGeometry.Spec.map_algebraMap_residueField_closedPoint`: the closed point of
  `Spec κ(p)` lies over the prime `p` of `R`.

The residue field map `f.residueFieldMap x` has source `κ(f x)`. When `f x` is known to equal a
point `y` only propositionally, for instance when `f` is an automorphism fixing `x`, it is
composed with `Scheme.residueFieldCongr` to give a map `κ(y) ⟶ κ(x)`. The lemmas
`Scheme.Hom.residueFieldCongr_inv_residueFieldMap_comp` and its companions compute such composites
without the casts that a direct rewrite of `f x` to `y` would produce.

A morphism surjective on stalks induces isomorphisms of residue fields. In a fibre product,
if one of the two points has unchanged residue field over the base, the pair has a unique lift
and the other projection preserves its residue field. These facts allow elementary étale
neighbourhoods to be refined without splitting their distinguished points.

The pullback arguments use Mathlib's `Scheme.Pullback.Triplet.tensor` description of the points
over a pair as the spectrum of the tensor product of their residue fields.

The two results on natural numbers only use that a ring homomorphism between fields, such as
Mathlib's `Scheme.Hom.residueFieldMap`, preserves natural number casts and is injective.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- If `N` is invertible in the residue field at `f x`, it is invertible in the residue field
at `x`. -/
theorem Scheme.Hom.natCast_residueField_ne_zero {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {N : ℕ}
    (hN : (N : Y.residueField (f x)) ≠ 0) : (N : X.residueField x) ≠ 0 := by
  rw [← map_natCast (f.residueFieldMap x).hom]
  exact (map_ne_zero _).mpr hN

/-- If `N` is invertible in a field `K`, it is invertible in the residue field of `Spec K`. -/
theorem Spec.natCast_residueField_ne_zero {K : Type u} [Field K] {N : ℕ} (hN : (N : K) ≠ 0)
    (s : Spec (.of K)) : (N : (Spec (.of K)).residueField s) ≠ 0 := by
  rw [← map_natCast ((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec (.of K)).presheaf.germ ⊤ s trivial ≫ (Spec (.of K)).residue s).hom]
  exact (map_ne_zero _).mpr hN

section residueFieldCongr

variable {X Y Z : Scheme.{u}}

/-- The residue field map of a composite, with sources identified along `f x = y` and `g y = z`,
is the composite of the residue field maps. -/
theorem Scheme.Hom.residueFieldCongr_inv_residueFieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) {x : X}
    {y : Y} {z : Z} (hf : f x = y) (hg : g y = z) (hfg : (f ≫ g) x = z) :
    (Z.residueFieldCongr hfg).inv ≫ (f ≫ g).residueFieldMap x =
      ((Z.residueFieldCongr hg).inv ≫ g.residueFieldMap y) ≫
        (Y.residueFieldCongr hf).inv ≫ f.residueFieldMap x := by
  subst hf hg
  simp

/-- Equal morphisms have equal residue field maps, with sources identified along `f x = y`. -/
theorem Scheme.Hom.residueFieldCongr_inv_residueFieldMap_congr {f f' : X ⟶ Y} (e : f = f')
    {x : X} {y : Y} (h : f x = y) (h' : f' x = y) :
    (Y.residueFieldCongr h).inv ≫ f.residueFieldMap x =
      (Y.residueFieldCongr h').inv ≫ f'.residueFieldMap x := by
  subst e
  rfl

/-- The residue field map of the identity, with source identified along `x = x'`, is the
identification `κ(x') ≅ κ(x)`. -/
theorem Scheme.residueFieldCongr_inv_residueFieldMap_id {x x' : X} (h : (𝟙 X : X ⟶ X) x = x') :
    (X.residueFieldCongr h).inv ≫ (𝟙 X : X ⟶ X).residueFieldMap x =
      (X.residueFieldCongr (h.symm : x' = x)).hom := by
  subst h
  simp

/-- The residue field map at `x`, with source identified along `f x = y`, sends the value at `y`
of a global function `a` to the value at `x` of its pullback `f^*(a)`. -/
theorem Scheme.Hom.residueFieldCongr_inv_residueFieldMap_Γevaluation (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) (a : Γ(Y, ⊤)) :
    ((Y.residueFieldCongr h).inv ≫ f.residueFieldMap x) (Y.Γevaluation y a) =
      X.Γevaluation x (f.appTop a) := by
  subst h
  simp [Scheme.Γevaluation_naturality_apply]

end residueFieldCongr

/-- The point of `Spec Γ(X, ⊤)` under `x` is the prime ideal of global functions vanishing at
`x`. -/
theorem Scheme.toSpecΓ_apply_asIdeal (X : Scheme.{u}) (x : X) :
    (X.toSpecΓ x).asIdeal = RingHom.ker (X.Γevaluation x).hom := by
  ext a
  -- A global function lies in this prime iff `x` is not in its basic open, iff its value at `x`
  -- vanishes.
  have h : x ∈ X.basicOpen a ↔ a ∉ (X.toSpecΓ x).asIdeal := by
    rw [← X.toSpecΓ_preimage_basicOpen a]
    exact PrimeSpectrum.mem_basicOpen a (X.toSpecΓ x)
  rw [RingHom.mem_ker]
  exact (not_not.symm.trans h.not.symm).trans
    (X.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) x trivial a).symm

/-- A ring map out of a residue field of `Spec R` is determined by its values on the elements
of `R`. -/
theorem Spec.residueField_hom_ext {R : CommRingCat.{u}} {p : Spec R} {K : CommRingCat.{u}}
    {α β : (Spec R).residueField p ⟶ K}
    (h : (Spec R).Γevaluation p ≫ α = (Spec R).Γevaluation p ≫ β) : α = β := by
  rw [← cancel_epi (Scheme.Spec.residueFieldIso R p).inv]
  -- The residue field is `p.asIdeal.ResidueField`, whose ring maps are determined on `R`.
  have h' := congr((Scheme.ΓSpecIso R).inv ≫ $h)
  ext1
  have := p.isPrime
  refine Ideal.ResidueField.ringHom_ext (I := p.asIdeal) ?_
  ext a
  have e : (Scheme.Spec.residueFieldIso R p).inv (algebraMap R _ a) =
      (Spec R).Γevaluation p ((Scheme.ΓSpecIso R).inv a) :=
    congr($(Scheme.Spec.algebraMap_residueFieldIso_inv R p).hom a)
  simpa [e] using congr($(h').hom a)

/-- The closed point of `Spec κ(p)` lies over `p` in `Spec R`. -/
@[simp]
theorem Spec.map_algebraMap_residueField_closedPoint {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) :
    Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
      (IsLocalRing.closedPoint p.asIdeal.ResidueField) = p :=
  -- `p` is the only point of `Spec R` in the image of `Spec κ(p)`.
  -- `Spec.map_apply` is applied as a term: `rw` cannot find it, since the closed point is typed
  -- as a point of `PrimeSpectrum κ(p)` rather than of `Spec (.of κ(p))`.
  (Spec.map_apply _ _).trans ((PrimeSpectrum.residueField_comap p).subset ⟨_, rfl⟩)

/-- On a quasi-affine scheme, a ring map out of the residue field `κ(x)` is determined by its
values on global functions evaluated at `x`. -/
theorem Scheme.residueField_hom_ext {X : Scheme.{u}} [X.IsQuasiAffine] {x : X}
    {K : CommRingCat.{u}} {α β : X.residueField x ⟶ K}
    (h : X.Γevaluation x ≫ α = X.Γevaluation x ≫ β) : α = β := by
  -- `X ⟶ Spec Γ(X, ⊤)` is an open immersion, so it induces an isomorphism of residue fields.
  have h₁ := Scheme.Γevaluation_naturality X.toSpecΓ x
  rw [Scheme.toSpecΓ_appTop] at h₁
  rw [← cancel_epi (X.toSpecΓ.residueFieldMap x)]
  refine Spec.residueField_hom_ext ?_
  rw [reassoc_of% h₁, reassoc_of% h₁, h]

/-- The geometric point of `X` over `x`: the morphism `Spec κ(x)ᵃˡᵍ ⟶ X` from the spectrum of an
algebraic closure of the residue field at `x`, through `X.fromSpecResidueField x`. -/
noncomputable def Scheme.fromSpecAlgebraicClosure (X : Scheme.{u}) (x : X) :
    Spec (.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫ X.fromSpecResidueField x

/-- The geometric point over `x` factors through `X.fromSpecResidueField x`. -/
theorem Scheme.fromSpecAlgebraicClosure_def (X : Scheme.{u}) (x : X) :
    X.fromSpecAlgebraicClosure x =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫
        X.fromSpecResidueField x :=
  (rfl)

/-- Every point of `Spec κ(x)ᵃˡᵍ` maps to `x` under the geometric point over `x`. -/
@[simp]
theorem Scheme.fromSpecAlgebraicClosure_apply (X : Scheme.{u}) (x : X)
    (p : Spec (.of (AlgebraicClosure (X.residueField x)))) :
    X.fromSpecAlgebraicClosure x p = x :=
  Scheme.fromSpecResidueField_apply x _

/-- The geometric point over `x` has image exactly `{x}`. -/
@[simp]
theorem Scheme.range_fromSpecAlgebraicClosure (X : Scheme.{u}) (x : X) :
    Set.range (X.fromSpecAlgebraicClosure x) = {x} :=
  Set.range_eq_singleton (X.fromSpecAlgebraicClosure_apply x)

/-- Two ring maps out of the residue field `κ(x)` agree once their spectra agree after
composition with the canonical morphism `Spec κ(x) ⟶ X`. -/
theorem Scheme.eq_of_SpecMap_comp_fromSpecResidueField {X : Scheme.{u}} {x : X}
    {R : CommRingCat.{u}} {a b : X.residueField x ⟶ R}
    (h : Spec.map a ≫ X.fromSpecResidueField x = Spec.map b ≫ X.fromSpecResidueField x) :
    a = b :=
  Spec.map_injective ((cancel_mono _).mp h)

/-- A morphism surjective on stalks induces isomorphisms on residue fields. -/
instance Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ((f.residueDegree_eq_one_iff x).mp
      (f.residueDegree_eq_one_of_surjectiveOnStalks x))

/-- If a composite preserves the residue field at a point, the second morphism preserves
the residue field at the image point. In particular, this cancels an open immersion from
a composite. -/
theorem Scheme.Hom.isIso_residueFieldMap_of_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [IsIso ((f ≫ g).residueFieldMap x)] : IsIso (g.residueFieldMap (f x)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(g.residueFieldMap (f x)).hom.injective, ?_⟩
  have h := (ConcreteCategory.bijective_of_isIso ((f ≫ g).residueFieldMap x)).surjective
  rw [Scheme.residueFieldMap_comp] at h
  -- Identify the source fields at (f ≫ g) x and g (f x), so function cancellation applies.
  change Function.Surjective ((f.residueFieldMap x).hom ∘
    (g.residueFieldMap (f x)).hom) at h
  exact h.of_comp_left (f.residueFieldMap x).hom.injective

open IsLocalRing in
/-- A lift of a morphism `Spec A ⟶ X` inducing an isomorphism of residue fields passes through a
point with unchanged residue field: if `A` is local, `φ : 𝒪_{X,x} → A` is a local homomorphism
inducing an isomorphism of residue fields, and `s : Spec A ⟶ U` lifts the morphism
`Spec A ⟶ X` given by `φ` along `f`, then `s` maps the closed point to a preimage of `x` at which
`f` induces an isomorphism of residue fields. -/
theorem Scheme.Hom.isIso_residueFieldMap_of_lift {X U : Scheme.{u}} (f : U ⟶ X) {x : X}
    {A : Type u} [CommRing A] [IsLocalRing A] (φ : X.presheaf.stalk x ⟶ CommRingCat.of A)
    [IsLocalHom φ.hom]
    (hφ : Function.Bijective (ResidueField.map φ.hom)) (s : Spec (.of A) ⟶ U)
    (hs : s ≫ f = Spec.map φ ≫ X.fromSpecStalk x) :
    f (s (closedPoint A)) = x ∧ IsIso (f.residueFieldMap (s (closedPoint A))) := by
  -- Read off the point and the local homomorphism of `s ≫ f` from `Spec A`.
  have h := (SpecToEquivOfLocalRing X (.of A)).apply_symm_apply
    ⟨x, φ, ‹_›⟩
  rw [show (SpecToEquivOfLocalRing X (.of A)).symm ⟨x, φ, ‹_›⟩ =
    s ≫ f from hs.symm] at h
  obtain ⟨hx, hφ'⟩ := SpecToEquivOfLocalRing_eq_iff.mp h
  -- The components of `SpecToEquivOfLocalRing` are by definition the image of the closed point
  -- and `stalkClosedPointTo`.
  change f (s (closedPoint A)) = x at hx
  subst hx
  change Scheme.stalkClosedPointTo (s ≫ f) = _ ≫ φ at hφ'
  rw [Scheme.stalkClosedPointTo_comp, TopCat.Presheaf.stalkCongr_hom] at hφ'
  -- The specialization `x ⤳ x` in `hφ'` is stated for `(s ≫ f) c` rather than `f (s c)`, so
  -- `stalkSpecializes_refl` only matches up to unfolding the composite.
  erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at hφ'
  -- `κ(f (s c)) → κ(s c) → κ(A)` is the bijection induced by `φ`.
  have key (y) : ResidueField.map (Scheme.stalkClosedPointTo s).hom
      (f.residueFieldMap (s (closedPoint A)) y) = ResidueField.map φ.hom y := by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    -- `f.residueFieldMap` is by definition the map of residue fields induced by `f.stalkMap`.
    change ResidueField.map _ (ResidueField.map _ (IsLocalRing.residue _ y)) =
      ResidueField.map _ (IsLocalRing.residue _ y)
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue,
      ← CommRingCat.comp_apply, hφ']
  refine ⟨rfl, (ConcreteCategory.isIso_iff_bijective _).mpr ⟨RingHom.injective _, ?_⟩⟩
  refine Function.Surjective.of_comp_left (f := ResidueField.map
    (Scheme.stalkClosedPointTo s).hom) (fun z ↦ ?_) (RingHom.injective _)
  obtain ⟨y, rfl⟩ := hφ.2 z
  exact ⟨y, key y⟩

namespace Scheme.Pullback

open Limits

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- Tensoring with an unchanged residue field leaves the other residue field unchanged. -/
instance Triplet.isIso_tensorInl (T : Triplet f g) [IsIso (g.residueFieldMap T.y)] :
    IsIso T.tensorInl := by
  -- Expose the pushout inclusion so that stability of isomorphisms under pushout applies.
  dsimp only [Triplet.tensorInl, Triplet.tensor]
  infer_instance

/-- If the residue field of `y` is unchanged over the base, a pair `(x, y)` has at most one
lift to the fibre product. -/
theorem eq_of_fst_eq_snd_eq_of_isIso {z z' : ↑(pullback f g)}
    (hx : pullback.fst f g z = pullback.fst f g z')
    (hy : pullback.snd f g z = pullback.snd f g z')
    [IsIso (g.residueFieldMap (pullback.snd f g z'))] : z = z' := by
  let T := Triplet.ofPoint z'
  have : IsIso (g.residueFieldMap T.y) := by
    have hy : T.y = pullback.snd f g z' := Triplet.ofPoint_y z'
    rw [hy]
    infer_instance
  have : Subsingleton (Spec T.tensor) :=
    (Scheme.homeoOfIso (asIso (Spec.map T.tensorInl))).injective.subsingleton
  have H (T' : Triplet f g) (p : Spec T'.tensor) (hT : T' = T) :
      T'.SpecTensorTo p = z' := by
    subst T'
    exact (congrArg T.SpecTensorTo (Subsingleton.elim p (SpecOfPoint z'))).trans
      (SpecTensorTo_SpecOfPoint z')
  exact (SpecTensorTo_SpecOfPoint z).symm.trans
    (H _ (SpecOfPoint z) (Triplet.ext hx hy))

/-- Base change by a point with unchanged residue field preserves the residue field at every
point above it. No finiteness or étaleness hypothesis is needed. -/
theorem isIso_residueFieldMap_fst (z : ↑(pullback f g))
    [IsIso (g.residueFieldMap (pullback.snd f g z))] :
    IsIso ((pullback.fst f g).residueFieldMap z) := by
  let T := Triplet.ofPoint z
  have : IsIso (g.residueFieldMap T.y) := by
    have hy : T.y = pullback.snd f g z := Triplet.ofPoint_y z
    rw [hy]
    infer_instance
  have : SurjectiveOnStalks (T.SpecTensorTo ≫ pullback.fst f g) := by
    rw [T.specTensorTo_fst]
    infer_instance
  have : SurjectiveOnStalks T.SpecTensorTo := .of_comp _ (pullback.fst f g)
  have h := T.SpecTensorTo.isIso_residueFieldMap_of_comp (pullback.fst f g) (SpecOfPoint z)
  have hz : T.SpecTensorTo (SpecOfPoint z) = z := SpecTensorTo_SpecOfPoint z
  rwa [hz] at h

end Scheme.Pullback

section FromSpecResidueField

variable {X : Scheme.{u}} (x : X)

/-- The closed point of `Spec κ(x)` maps to `x`, so it lies over every open containing `x`. -/
lemma Scheme.fromSpecResidueField_closedPoint_mem {V : X.Opens} (hx : x ∈ V) :
    X.fromSpecResidueField x (IsLocalRing.closedPoint (X.residueField x)) ∈ V := by
  convert hx using 1
  exact Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint (X.residueField x))

/-- The inverse image of an open containing `x` under `Spec κ(x) ⟶ X` is everything. -/
lemma Scheme.fromSpecResidueField_preimage_eq_top {V : X.Opens} (hx : x ∈ V) :
    X.fromSpecResidueField x ⁻¹ᵁ V = ⊤ :=
  Scheme.preimage_eq_top_of_closedPoint_mem _ (fromSpecResidueField_closedPoint_mem x hx)

/-- On an open `V` containing `x`, the morphism `Spec κ(x) ⟶ X` sends a function to its value at
`x`, as a global function on `Spec κ(x)`. -/
lemma Scheme.fromSpecResidueField_appLE {V : X.Opens} (hx : x ∈ V)
    (h : (⊤ : (Spec (X.residueField x)).Opens) ≤ X.fromSpecResidueField x ⁻¹ᵁ V) :
    (X.fromSpecResidueField x).appLE V ⊤ h =
      X.evaluation V x hx ≫ (Scheme.ΓSpecIso (X.residueField x)).inv := by
  have hV := fromSpecResidueField_closedPoint_mem x hx
  have : IsLocalHom (X.residue x).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  -- `Spec κ(x) ⟶ X` is `Spec κ(x) ⟶ Spec 𝒪_{X,x} ⟶ X`, whose action on sections near the
  -- closed point is computed by Mathlib's `Scheme.germ_stalkClosedPointTo`.
  rw [Iso.eq_comp_inv, ← X.germ_residue x hx,
    ← Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (X.residue x) V hV]
  refine Eq.trans ?_ (Scheme.germ_stalkClosedPointTo
    (Spec.map (X.residue x) ≫ X.fromSpecStalk x) V hV).symm
  rw [Scheme.Hom.appLE, Category.assoc, Iso.trans_hom, Functor.mapIso_hom]
  congr 2

/-- For an open `V` containing `x`, the functions on `ι⁻¹ V = Spec κ(x)` are `κ(x)`, where
`ι : Spec κ(x) ⟶ X`. -/
noncomputable def Scheme.residueFieldSectionsIso {V : X.Opens} (hx : x ∈ V) :
    Γ(Spec (X.residueField x), X.fromSpecResidueField x ⁻¹ᵁ V) ≅ X.residueField x :=
  ((Spec (X.residueField x)).presheaf.mapIso
    (eqToIso (fromSpecResidueField_preimage_eq_top x hx)).op).symm ≪≫
    Scheme.ΓSpecIso (X.residueField x)

/-- The inverse of `Scheme.residueFieldSectionsIso` is restriction from `⊤` to `ι⁻¹ V`. -/
lemma Scheme.residueFieldSectionsIso_inv {V : X.Opens} (hx : x ∈ V) :
    (X.residueFieldSectionsIso x hx).inv = (Scheme.ΓSpecIso (X.residueField x)).inv ≫
      (Spec (X.residueField x)).presheaf.map (homOfLE le_top).op := by
  rw [residueFieldSectionsIso, Iso.trans_inv]
  rfl

/-- The identifications `Scheme.residueFieldSectionsIso` commute with restriction. -/
@[reassoc (attr := simp)]
lemma Scheme.residueFieldSectionsIso_map {U V : X.Opens} (hU : x ∈ U) (hV : x ∈ V)
    (j : X.fromSpecResidueField x ⁻¹ᵁ U ⟶ X.fromSpecResidueField x ⁻¹ᵁ V) :
    (Spec (X.residueField x)).presheaf.map j.op ≫ (X.residueFieldSectionsIso x hU).hom =
      (X.residueFieldSectionsIso x hV).hom := by
  rw [residueFieldSectionsIso, residueFieldSectionsIso, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc]
  rfl

/-- On an open `V` containing `x`, the morphism `ι : Spec κ(x) ⟶ X` acts on sections by
evaluation at `x`. -/
@[reassoc (attr := simp)]
lemma Scheme.fromSpecResidueField_app_residueFieldSectionsIso_hom {V : X.Opens} (hx : x ∈ V) :
    (X.fromSpecResidueField x).app V ≫ (X.residueFieldSectionsIso x hx).hom =
      X.evaluation V x hx := by
  rw [← Iso.eq_comp_inv, residueFieldSectionsIso_inv, ← Category.assoc,
    ← fromSpecResidueField_appLE x hx (fromSpecResidueField_preimage_eq_top x hx).ge,
    Scheme.Hom.appLE_map]
  rfl

end FromSpecResidueField

end AlgebraicGeometry

namespace RingHom

open AlgebraicGeometry

universe u

/-- For a ring map `φ : R →+* S` and a point `x` of `Spec S`, the residue field map of
`Spec.map φ` at `x` is an isomorphism iff the induced map `κ(p) → κ(x)` is bijective, where
`p = φ⁻¹ x` is the image point. -/
theorem isIso_SpecMap_residueFieldMap_iff {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : Spec (.of S)) (p : Ideal R) [p.IsPrime] (hp : p = x.asIdeal.comap φ) :
    haveI := x.isPrime
    IsIso ((Spec.map (CommRingCat.ofHom φ)).residueFieldMap x) ↔
      Function.Bijective (Ideal.ResidueField.map p x.asIdeal φ hp) := by
  have := x.isPrime
  -- The residue field isomorphisms of `Spec R` are indexed by the image point, which is
  -- `x.asIdeal.comap φ` by `Spec.map_apply`.
  have hp' : p = ((Spec.map (CommRingCat.ofHom φ)) x).asIdeal :=
    hp.trans (congrArg PrimeSpectrum.asIdeal (Spec.map_apply (CommRingCat.ofHom φ) x)).symm
  subst hp'
  -- Up to the residue field isomorphisms, the residue field map is `Ideal.ResidueField.map`.
  have key : (Spec.map (CommRingCat.ofHom φ)).residueFieldMap x =
      (Scheme.Spec.residueFieldIso (.of R) _).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map _ x.asIdeal φ hp) ≫
        (Scheme.Spec.residueFieldIso (.of S) x).inv := by
    ext y
    obtain ⟨a, rfl⟩ := (Spec (.of R)).residue_surjective _ y
    have h := congr($(Scheme.residue_residueFieldMap (Spec.map (CommRingCat.ofHom φ)) x) a)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact h.trans (congrArg (IsLocalRing.residue _)
      (Scheme.localRingHom_comp_stalkIso_apply (CommRingCat.ofHom φ) x a).symm)
  rw [key, isIso_comp_left_iff, isIso_comp_right_iff, ConcreteCategory.isIso_iff_bijective]
  rfl

end RingHom

namespace AlgebraicGeometry

universe u

/-- The map `Spec R ⟶ U ⊆ S` induced by the structure map of a `Γ(S, U)`-algebra `R` on an
affine open `U` induces an isomorphism of residue fields at a point `u` over the prime `s` of
`Γ(S, U)` as soon as `κ(s) ≅ κ(u)`. -/
theorem IsAffineOpen.isIso_residueFieldMap_spec_algebraMap_comp_fromSpec {S : Scheme.{u}}
    {U : S.Opens} (hU : IsAffineOpen U) {s : S} (hs : s ∈ U) (R : Type u) [CommRing R]
    [Algebra Γ(S, U) R] (u : Spec ↧R)
    [u.asIdeal.LiesOver (hU.primeIdealOf ⟨s, hs⟩).asIdeal]
    (hres : haveI := u.isPrime
      Function.Bijective (Ideal.ResidueField.mapₐ (hU.primeIdealOf ⟨s, hs⟩).asIdeal
        u.asIdeal (Algebra.ofId _ _) (u.asIdeal.over_def _))) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) R)) ≫ hU.fromSpec).residueFieldMap
      u) := by
  have := u.isPrime
  -- the residue field map of the open immersion `hU.fromSpec`, then 00UJ.
  have := ((algebraMap Γ(S, U) R).isIso_SpecMap_residueFieldMap_iff u _
    (u.asIdeal.over_def _)).mpr hres
  rw [Scheme.residueFieldMap_comp]
  have h₁ : IsIso (hU.fromSpec.residueFieldMap
    ((Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) R))) u)) := inferInstance
  exact IsIso.comp_isIso' h₁ this

end AlgebraicGeometry
