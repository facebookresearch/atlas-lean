/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveSchemeChartAtInfinity
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension

/-!
# Integral Weierstrass models of an elliptic curve over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and residue field
`k = IsLocalRing.ResidueField R`, and let `E` be an elliptic curve over `K`, presented by a
Weierstrass equation (`E : WeierstrassCurve K` with `[E.IsElliptic]`), with scheme
`E.ProjectiveScheme` and identity section `E.zeroSection`. This file states the definitions of
planar and abstract integral Weierstrass models of `E` over `R`, and of their morphisms.

Generic and special fibres are the pullbacks along `Spec K → Spec R` and `Spec k → Spec R`.
(Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber` takes the fibre over a point `y` along
`Spec κ(y) → Spec R`; at the generic and closed points `κ(y)` is canonically isomorphic to `K` and
`k`, but not definitionally equal to them, so the given fields are used here, as in the source.)

## Main definitions

* `AlgebraicGeometry.baseChangeSection`: the base change `T → X ×_S T` of a section of `X → S`.
* `WeierstrassCurve.PlanarWeierstrassModel`: a planar integral Weierstrass model of `E` over `R`.
* `WeierstrassCurve.WeierstrassModel`: an abstract integral Weierstrass model of `E` over `R`,
  also called a Weierstrass model.
* `WeierstrassCurve.WeierstrassModel.smoothLocus`: its smooth locus.
* `WeierstrassCurve.PlanarWeierstrassModel.Hom`, `WeierstrassCurve.WeierstrassModel.Hom`:
  morphisms of models, with the resulting categories.

## References

* B. Conrad, *Minimal models for elliptic curves*, notes (version of 21 November 2015),
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>: Definition 2.1 and Definition 2.4,
  p. 2; the name "Weierstrass model" for an abstract integral Weierstrass model, p. 6.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X S T : Scheme.{u}}

/-- **The base change of a section.** For a morphism `g : X ⟶ S`, a section `s : S ⟶ X` of `g`
(`s ≫ g = 𝟙 S`) and a morphism `b : T ⟶ S`, this is the section `T ⟶ X ×_S T` of the second
projection whose first component is `b ≫ s`. -/
noncomputable def baseChangeSection (g : X ⟶ S) (s : S ⟶ X) (hs : s ≫ g = 𝟙 S) (b : T ⟶ S) :
    T ⟶ pullback g b :=
  pullback.lift (b ≫ s) (𝟙 T) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem baseChangeSection_fst (g : X ⟶ S) (s : S ⟶ X) (hs : s ≫ g = 𝟙 S) (b : T ⟶ S) :
    baseChangeSection g s hs b ≫ pullback.fst g b = b ≫ s :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeSection_snd (g : X ⟶ S) (s : S ⟶ X) (hs : s ≫ g = 𝟙 S) (b : T ⟶ S) :
    baseChangeSection g s hs b ≫ pullback.snd g b = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- **The base change of a morphism over `S`.** For `S`-schemes `f : X ⟶ S`, `g : Y ⟶ S`, an
`S`-morphism `φ : X ⟶ Y` (`φ ≫ g = f`) and a morphism `b : T ⟶ S`, this is the induced
`T`-morphism `X ×_S T ⟶ Y ×_S T`: the underlying morphism of the image of `φ` under Mathlib's
pullback functor `Over.pullback b : Over S ⥤ Over T`. -/
noncomputable def baseChangeMap {Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (φ : X ⟶ Y)
    (h : φ ≫ g = f) (b : T ⟶ S) : pullback f b ⟶ pullback g b :=
  ((Over.pullback b).map (Over.homMk φ h : Over.mk f ⟶ Over.mk g)).left

@[reassoc (attr := simp)]
theorem baseChangeMap_fst {Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (φ : X ⟶ Y)
    (h : φ ≫ g = f) (b : T ⟶ S) :
    baseChangeMap f g φ h b ≫ pullback.fst g b = pullback.fst f b ≫ φ := by
  simp [baseChangeMap]

@[reassoc (attr := simp)]
theorem baseChangeMap_snd {Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (φ : X ⟶ Y)
    (h : φ ≫ g = f) (b : T ⟶ S) :
    baseChangeMap f g φ h b ≫ pullback.snd g b = pullback.snd f b := by
  simp [baseChangeMap]

/-- The base change of the identity is the identity (functoriality of `Over.pullback b`). -/
@[simp]
theorem baseChangeMap_id (f : X ⟶ S) (b : T ⟶ S) :
    baseChangeMap f f (𝟙 X) (Category.id_comp f) b = 𝟙 _ := by
  simp only [baseChangeMap]
  rw [show (Over.homMk (𝟙 X) (Category.id_comp f) : Over.mk f ⟶ Over.mk f) = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id]
  rfl

/-- The base change of a composite is the composite (functoriality of `Over.pullback b`). -/
theorem baseChangeMap_comp {Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (k : Z ⟶ S) (φ : X ⟶ Y)
    (ψ : Y ⟶ Z) (hφ : φ ≫ g = f) (hψ : ψ ≫ k = g) (b : T ⟶ S) :
    baseChangeMap f k (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) b =
      baseChangeMap f g φ hφ b ≫ baseChangeMap g k ψ hψ b := by
  simp only [baseChangeMap]
  rw [← Over.comp_left, ← CategoryTheory.Functor.map_comp]
  rfl

end AlgebraicGeometry

open AlgebraicGeometry

namespace WeierstrassCurve

variable (R : Type u) [CommRing R] {K : Type u} [Field K] [Algebra R K] (E : WeierstrassCurve K)

/-- **Planar integral Weierstrass model** (B. Conrad, *Minimal models for elliptic curves*,
Definition 2.1, p. 2). Let `R` be a discrete valuation ring with fraction field `K`, and let `E`
be an elliptic curve over `K`, presented by a Weierstrass equation. A planar integral Weierstrass
model of `E` over `R` consists of

* a Weierstrass curve `W` over `R`, i.e. coefficients `a₁, a₂, a₃, a₄, a₆ ∈ R` of the equation
  `y² + (a₁ x + a₃) y = x³ + a₂ x² + a₄ x + a₆`; its scheme `W.ProjectiveScheme` is the closed
  subscheme of the projective plane over `R` cut out by the homogenized equation;
* an isomorphism `i : W_K ≅ E` of `K`-schemes, where `W_K` is the generic fibre, the pullback of
  `W.ProjectiveScheme → Spec R` along `Spec K → Spec R`, and `E` is `E.ProjectiveScheme`,
  carrying the point `[0 : 1 : 0]` of `W_K` (the base change of `W.zeroSection`) to the identity
  `E.zeroSection`.

No condition on the discriminant of `W` is imposed; the source imposes none either.

On the presentation of `E`: the source's elliptic curve over `K` is an abstract one (a smooth
proper geometrically connected curve of genus `1` with a rational point). Here `E` is given by a
Weierstrass equation with invertible discriminant, whose scheme `E.ProjectiveScheme` with the
section `E.zeroSection` is such a curve. Every elliptic curve over `K` is isomorphic to one of this
form (Riemann–Roch), so this is a choice of presentation of the input, not a restriction up to
isomorphism. -/
structure PlanarWeierstrassModel [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    [E.IsElliptic] where
  /-- The integral Weierstrass equation. -/
  W : WeierstrassCurve R
  /-- The isomorphism `W_K ≅ E` from the generic fibre. -/
  i : pullback W.projectiveSchemeToSpec (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
    E.ProjectiveScheme
  /-- `i` is an isomorphism of `K`-schemes. -/
  i_hom_projectiveSchemeToSpec : i.hom ≫ E.projectiveSchemeToSpec = pullback.snd _ _
  /-- `i` carries `[0 : 1 : 0]` to the identity of `E`. -/
  zeroSection_i_hom : baseChangeSection W.projectiveSchemeToSpec W.zeroSection
    W.zeroSection_projectiveSchemeToSpec (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
      i.hom = E.zeroSection

/-- **Abstract integral Weierstrass model**, also called a **Weierstrass model** (B. Conrad,
*Minimal models for elliptic curves*, Definition 2.4, p. 2; the name, p. 6). Let `R` be a discrete
valuation ring with fraction field `K` and residue field `k`, and let `E` be an elliptic curve
over `K`, presented by a Weierstrass equation (see `WeierstrassCurve.PlanarWeierstrassModel` for
why this matches the source). An abstract integral Weierstrass model of `E` over `R` consists of

* a scheme `𝒲` with a proper flat morphism `f : 𝒲 ⟶ Spec R`;
* an isomorphism `i : 𝒲_K ≅ E` of `K`-schemes, where `𝒲_K` is the generic fibre, the pullback of
  `f` along `Spec K → Spec R`, and `E` is `E.ProjectiveScheme`;

such that

* `𝒲` is normal. Mathlib has no predicate for normal schemes; this is encoded as: every stalk of
  `𝒲` is an integrally closed domain (the definition of a normal scheme: every local ring is a
  normal domain);
* the special fibre `𝒲_k`, the pullback of `f` along `Spec k → Spec R`, is `1`-dimensional
  (`topologicalKrullDim` of its underlying space is `1`) and geometrically irreducible (Mathlib's
  `GeometricallyIrreducible` for the morphism `𝒲_k ⟶ Spec k`: its base change to every field is
  irreducible);
* `𝒲_k ⟶ Spec k` is smooth at the reduction `ε(k)` of `ε`, i.e. that point lies in Mathlib's
  `Scheme.Hom.smoothLocus` of `𝒲_k ⟶ Spec k` (the points where the stalk map is formally smooth;
  as `𝒲_k ⟶ Spec k` is locally of finite presentation, these are the points where it is smooth);

where `ε : Spec R ⟶ 𝒲` is a section of `f` whose generic fibre `Spec K ⟶ 𝒲_K` is carried by `i`
to the identity `E.zeroSection`, and `ε(k)` is the image of the point of `Spec k` under the
special fibre `Spec k ⟶ 𝒲_k` of `ε`.

Deviation: the source speaks of "the unique `ε ∈ 𝒲(R) = E(K)` extending the identity of `E`".
Here `ε` is a field (data) with the extension property. Its existence follows from properness
(valuative criterion) and its uniqueness from separatedness; neither is a field, and they are
not proved here. Since `ε` is unique, including it as data does not change the notion. -/
structure WeierstrassModel [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    [E.IsElliptic] where
  /-- The total space of the model. -/
  𝒲 : Scheme.{u}
  /-- The structure morphism to `Spec R`. -/
  f : 𝒲 ⟶ Spec (CommRingCat.of R)
  /-- `f` is proper. -/
  [isProper : IsProper f]
  /-- `f` is flat. -/
  [flat : Flat f]
  /-- The isomorphism `𝒲_K ≅ E` from the generic fibre. -/
  i : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅ E.ProjectiveScheme
  /-- `i` is an isomorphism of `K`-schemes. -/
  i_hom_projectiveSchemeToSpec : i.hom ≫ E.projectiveSchemeToSpec = pullback.snd _ _
  /-- `𝒲` is normal: every stalk is an integrally closed domain. -/
  normal : ∀ x : 𝒲, IsDomain (𝒲.presheaf.stalk x) ∧ IsIntegrallyClosed (𝒲.presheaf.stalk x)
  /-- The special fibre is `1`-dimensional. -/
  topologicalKrullDim_specialFibre :
    topologicalKrullDim (pullback f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme.{u}) = 1
  /-- The special fibre is geometrically irreducible over `k`. -/
  geometricallyIrreducible_specialFibre :
    GeometricallyIrreducible (pullback.snd f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  /-- The section of `f` extending the identity of `E`. -/
  ε : Spec (CommRingCat.of R) ⟶ 𝒲
  /-- `ε` is a section of `f`. -/
  ε_f : ε ≫ f = 𝟙 _
  /-- The generic fibre of `ε` is carried by `i` to the identity of `E`. -/
  ε_i_hom : baseChangeSection f ε ε_f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ i.hom =
    E.zeroSection
  /-- The special fibre is smooth over `k` at the reduction `ε(k)` of `ε`. -/
  ε_mem_smoothLocus :
    (baseChangeSection f ε ε_f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).base
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) ∈
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).smoothLocus

namespace WeierstrassModel

attribute [instance] isProper flat

variable {R E} [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [E.IsElliptic]

/-- **The smooth locus of a Weierstrass model** (B. Conrad, *Minimal models for elliptic curves*,
p. 6): the open subscheme `𝒲^sm` of points of `𝒲` at which `f : 𝒲 ⟶ Spec R` is smooth
(Mathlib's `Scheme.Hom.smoothLocus`, the points where the stalk map of `f` is formally smooth;
`f` is locally of finite presentation, being proper over a noetherian base, so these are the points
where `f` is smooth). -/
noncomputable abbrev smoothLocus (M : E.WeierstrassModel R) : M.𝒲.Opens :=
  M.f.smoothLocus

/-- **Morphism of Weierstrass models** (B. Conrad, *Minimal models for elliptic curves*,
Definition 2.4, p. 2: a morphism is an `R`-morphism respecting the generic-fibre
identifications). A morphism `(𝒲, i) ⟶ (𝒲', i')` is an `R`-morphism `𝒲 ⟶ 𝒲'` whose generic
fibre `𝒲_K ⟶ 𝒲'_K` respects `i` and `i'`. No compatibility with the sections `ε`, `ε'` is
required, as in the source (it would follow from the uniqueness of `ε'`, not proved here). -/
@[ext]
structure Hom (M M' : E.WeierstrassModel R) where
  /-- The underlying morphism of schemes. -/
  hom : M.𝒲 ⟶ M'.𝒲
  /-- `hom` is an `R`-morphism. -/
  hom_f : hom ≫ M'.f = M.f
  /-- The generic fibre of `hom` respects `i` and `i'`. -/
  map_i_hom : baseChangeMap M.f M'.f hom hom_f
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ M'.i.hom = M.i.hom

attribute [reassoc (attr := simp)] Hom.hom_f

/-- Weierstrass models of `E` over `R` and their morphisms form a category. -/
noncomputable instance : Category (E.WeierstrassModel R) where
  Hom := Hom
  id M := ⟨𝟙 _, Category.id_comp _, by rw [baseChangeMap_id, Category.id_comp]⟩
  comp φ ψ := ⟨φ.hom ≫ ψ.hom, by simp, by
    rw [baseChangeMap_comp _ _ _ _ _ φ.2 ψ.2, Category.assoc, ψ.map_i_hom, φ.map_i_hom]⟩
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

@[simp]
theorem id_hom (M : E.WeierstrassModel R) : Hom.hom (𝟙 M) = 𝟙 M.𝒲 := rfl

@[simp]
theorem comp_hom {M M' M'' : E.WeierstrassModel R} (φ : M ⟶ M') (ψ : M' ⟶ M'') :
    Hom.hom (φ ≫ ψ) = Hom.hom φ ≫ Hom.hom ψ := rfl

end WeierstrassModel

namespace PlanarWeierstrassModel

variable {R E} [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [E.IsElliptic]

/-- **Morphism of planar Weierstrass models** (B. Conrad, *Minimal models for elliptic curves*,
Definition 2.1, p. 2: a morphism is an `R`-morphism respecting the generic-fibre
identifications). A morphism `(W, i) ⟶ (W', i')` is an `R`-morphism
`W.ProjectiveScheme ⟶ W'.ProjectiveScheme` whose generic fibre respects `i` and `i'`. It is not
required to come from a change of variables of the equations, as in the source. -/
@[ext]
structure Hom (M M' : E.PlanarWeierstrassModel R) where
  /-- The underlying morphism of schemes. -/
  hom : M.W.ProjectiveScheme ⟶ M'.W.ProjectiveScheme
  /-- `hom` is an `R`-morphism. -/
  hom_projectiveSchemeToSpec : hom ≫ M'.W.projectiveSchemeToSpec = M.W.projectiveSchemeToSpec
  /-- The generic fibre of `hom` respects `i` and `i'`. -/
  map_i_hom : baseChangeMap M.W.projectiveSchemeToSpec M'.W.projectiveSchemeToSpec hom
      hom_projectiveSchemeToSpec (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ M'.i.hom =
        M.i.hom

attribute [reassoc (attr := simp)] Hom.hom_projectiveSchemeToSpec

/-- Planar Weierstrass models of `E` over `R` and their morphisms form a category. -/
noncomputable instance : Category (E.PlanarWeierstrassModel R) where
  Hom := Hom
  id M := ⟨𝟙 _, Category.id_comp _, by rw [baseChangeMap_id, Category.id_comp]⟩
  comp φ ψ := ⟨φ.hom ≫ ψ.hom, by simp, by
    rw [baseChangeMap_comp _ _ _ _ _ φ.2 ψ.2, Category.assoc, ψ.map_i_hom, φ.map_i_hom]⟩
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

@[simp]
theorem id_hom (M : E.PlanarWeierstrassModel R) : Hom.hom (𝟙 M) = 𝟙 M.W.ProjectiveScheme := rfl

@[simp]
theorem comp_hom {M M' M'' : E.PlanarWeierstrassModel R} (φ : M ⟶ M') (ψ : M' ⟶ M'') :
    Hom.hom (φ ≫ ψ) = Hom.hom φ ≫ Hom.hom ψ := rfl

end PlanarWeierstrassModel

end WeierstrassCurve
