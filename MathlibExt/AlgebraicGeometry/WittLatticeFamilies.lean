/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import MathlibExt.LinearAlgebra.LocalizedLattices
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import MathlibExt.AlgebraicGeometry.PerfectSchemeModels

/-!
# Actual Witt-lattice family and bounded-representability contracts

Perfect F_p-algebras are actual commutative F_p-algebras with bijective
p-power Frobenius, including the zero algebra. Points are finite-projective
W(R)-lattices in the actual p-localized free module. Scalar base change
uses the actual Witt map and the span of its coordinate images.

The ordinary scalar-extension producer is an explicitly normalized input.
The remaining geometric representation is an actual perfect F_p scheme,
with a separate ordinary projective deperfection and its universal map.
Lattice points and naturality target the actual perfect scheme.
It does not assume representability or attach an arbitrary Grassmannian type.

Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*,
arXiv:1507.06490v3, Theorem1.1, pp1-2. Generic polynomial Grassmannians
and native Witt ring operations are already available source primitives;
this family comparison is their mixed-characteristic interface.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.WittLatticeFamilies

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.LinearAlgebra.LocalizedLattices

variable (p : ℕ) [Fact p.Prime]

/-- The actual perfect F_p-algebra objects, without excluding the zero algebra. -/
def IsPerfectAlgebra (R : CommAlgCat.{0} (ZMod p)) : Prop :=
  Function.Bijective (fun x : R ↦ x ^ p)

abbrev PerfectAlgebra := ObjectProperty.FullSubcategory (IsPerfectAlgebra p)

/-- The actual standard p-inverted ambient module and its lattice carrier. -/
abbrev WittLattice (R : PerfectAlgebra p) (n : ℕ) :=
  Lattice (WittVector p R.obj) (p : WittVector p R.obj) n

/-- The exact actual bounded lattice subfunctor. -/
abbrev BoundedLattice (R : PerfectAlgebra p) (n N : ℕ) :=
  {L : WittLattice p R n | IsBoundedBy _ _ _ L N}

/-- The specified Witt-map localization, keeping p fixed by the actual map. -/
def fractionMap {R S : PerfectAlgebra p} (f : R ⟶ S) :
    Localization.Away (p : WittVector p R.obj) →+*
      Localization.Away (p : WittVector p S.obj) :=
  Localization.awayLift
    ((algebraMap (WittVector p S.obj)
      (Localization.Away (p : WittVector p S.obj))).comp
        (WittVector.map f.hom.hom.toRingHom)) (p : WittVector p R.obj)
    (by
      have h : IsUnit (algebraMap (WittVector p S.obj)
          (Localization.Away (p : WittVector p S.obj)) (p : WittVector p S.obj)) :=
        IsLocalization.Away.algebraMap_isUnit
          (S := Localization.Away (p : WittVector p S.obj)) _
      simpa only [RingHom.comp_apply, map_natCast] using h)

/-- Scalar extension is the actual span of localized coordinate images. -/
def coordinateSpan {R S : PerfectAlgebra p} (f : R ⟶ S)
    {n : ℕ} (L : WittLattice p R n) :
    Submodule (WittVector p S.obj)
      (Fin n → Localization.Away (p : WittVector p S.obj)) :=
  Submodule.span _ {v | ∃ x : L.module,
    v = fun i ↦ fractionMap p f (x.val i)}

/-- Source-normalized scalar extension; no freely selected lattice map. -/
class BaseChange (n : ℕ) where
  map : ∀ {R S : PerfectAlgebra p}, (R ⟶ S) → WittLattice p R n → WittLattice p S n
  image : ∀ {R S : PerfectAlgebra p} (f : R ⟶ S) (L : WittLattice p R n),
    (map f L).module = coordinateSpan p f L
  map_id : ∀ {R : PerfectAlgebra p} (L : WittLattice p R n), map (𝟙 R) L = L
  map_comp : ∀ {R S T : PerfectAlgebra p} (f : R ⟶ S) (g : S ⟶ T)
    (L : WittLattice p R n), map (f ≫ g) L = map g (map f L)
  bounded : ∀ {R S : PerfectAlgebra p} (f : R ⟶ S) (L : WittLattice p R n)
    (N : ℕ), IsBoundedBy _ _ _ L N → IsBoundedBy _ _ _ (map f L) N

variable (n N : ℕ) [B : BaseChange p n]

/-- The actual bounded point map, with its fixed base-change image. -/
def boundedMap {R S : PerfectAlgebra p} (f : R ⟶ S) :
    BoundedLattice p R n N → BoundedLattice p S n N :=
  fun L ↦ ⟨B.map f L.val, B.bounded f L.val N L.property⟩

/-- The actual affine test object over the canonical prime field. -/
def testScheme (R : PerfectAlgebra p) : Over (Spec (.of (ZMod p))) :=
  Over.mk (Spec.algebraMap (ZMod p) R.obj)

/-- Its actual contravariant scheme map. -/
def testMap {R S : PerfectAlgebra p} (f : R ⟶ S) :
    testScheme p S ⟶ testScheme p R :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.hom.hom.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.hom.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) R.obj)) =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) S.obj))
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact f.hom.hom.commutes a)

/-- The actual perfect bounded scheme and its separate projective deperfection. -/
structure Representation where
  ordinaryModel : Over (Spec (.of (ZMod p)))
  projective : ProjectiveLineSystems.IsProjectiveVariety ordinaryModel
  [finitePresentation : LocallyOfFinitePresentation ordinaryModel.hom]
  perfection : PerfectSchemeModels.PerfectionModel p ordinaryModel
  points : ∀ R : PerfectAlgebra p,
    BoundedLattice p R n N ≃ (testScheme p R ⟶ perfection.scheme)
  naturality : ∀ {R S : PerfectAlgebra p} (f : R ⟶ S)
    (L : BoundedLattice p R n N),
    points S (boundedMap p n N f L) = testMap p f ≫ points R L

/-- The actual perfect geometric output; the ordinary model stays separate. -/
abbrev Representation.perfectScheme (M : Representation p n N) := M.perfection.scheme

end MathlibExt.AlgebraicGeometry.WittLatticeFamilies
