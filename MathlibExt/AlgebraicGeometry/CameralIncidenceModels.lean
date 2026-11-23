/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralReductiveSources
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

/-!
# Actual Borel incidence and the universal Cartan value map

The universal cameral scheme represents pairs of an actual
regular-centralizer plane and an actual Borel plane containing it.
Borel planes are etale-locally actual adjoint translates of the specified
maximal solvable subalgebra. The Cartan value morphism is normalized by
the actual quotient of that Borel by its derived subalgebra, on every
affine coefficient algebra and every actual adjoint trivialization.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections1.2--1.5,
11.1--11.3,12.5 and17.1--17.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CameralIncidenceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ExpansionParameterModels CameralTorusBands RegularCentralizerAffineModels
open SchemeLieJetFamilies CameralReductiveSources
open scoped TensorProduct

variable {k : Type} [Field k] {r : ℕ}
  {G : Over (Spec (.of k))} [GrpObj G]
  {V : Type} [LieRing V] [LieAlgebra k V] [FiniteDimensional k V]
  {L : AffineGroupLieModels.LieModel G V}
  {J : TangentFamilies G V L} {D : AdjointFamilies G V L J}
  {T : TorusTheory k r} {Gm : TorusTheory k 1}
  {W : Type} [Group W] [Fintype W] {R : Roots T Gm W}
  (S : Source G V L J D T Gm W R)

structure BorelSource where
  subalgebra : LieSubalgebra k V
  solvable : LieAlgebra.IsSolvable subalgebra
  maximal : ∀ b : LieSubalgebra k V, LieAlgebra.IsSolvable b →
    subalgebra ≤ b → b = subalgebra
  cartan : ∀ v : Fin r → k, S.cartan v ∈ subalgebra
  quotient : subalgebra →ₗ[k] (Fin r → k)
  cartan_quotient : ∀ v : Fin r → k, quotient ⟨S.cartan v, cartan v⟩ = v
  kernel : LinearMap.ker quotient =
    (LieAlgebra.derivedSeries k subalgebra 1).toSubmodule

variable {S} (B : BorelSource S)

def borelAt (A : CommAlgCat.{0} k) : Submodule A (LieAt V A) :=
  B.subalgebra.toSubmodule.baseChange A

abbrev BorelGrass (A : CommAlgCat.{0} k) :=
  Module.Grassmannian A (LieAt V A) (Module.finrank k V - Module.finrank k B.subalgebra)

structure BorelChart (A : CommAlgCat.{0} k) (P : BorelGrass B A) (p : PrimeSpectrum A) where
  algebra : CommAlgCat.{0} k
  map : A ⟶ algebra
  etale : Etale (Spec.map (CommRingCat.ofHom map.hom.toRingHom))
  point : PrimeSpectrum algebra
  point_eq : PrimeSpectrum.comap map.hom.toRingHom point = p
  conjugator : affine algebra ⟶ G
  normalized : (Module.Grassmannian.map map.hom P).toSubmodule =
    (borelAt B algebra).map (D.adjoint algebra conjugator).toLinearMap

structure BorelPlane (A : CommAlgCat.{0} k) where
  plane : BorelGrass B A
  charts : ∀ p : PrimeSpectrum A, Nonempty (BorelChart B A plane p)

def scalarModule (X : Over (Spec (.of k))) (M : ModuleCat.{0} k) : X.left.Modules :=
  (Scheme.Modules.pullback X.hom).obj ((tilde.functor (.of k)).obj M)

/-- The flag scheme, as the scheme representing Borel planes. Its tautological subbundle is
determined by this functor of points, so it is not recorded separately. -/
structure FlagScheme where
  scheme : Over (Spec (.of k))
  points : ∀ A : CommAlgCat.{0} k, (affine A ⟶ scheme) ≃ BorelPlane B A
  naturality : ∀ {A A' : CommAlgCat.{0} k} (u : A ⟶ A') (f : affine A ⟶ scheme),
    (points A' (affineMap u ≫ f)).plane = Module.Grassmannian.map u.hom (points A f).plane

variable (P : ParameterScheme (k := k) V r) (F : FlagScheme B)

structure CentralizerAction where
  [action : ModObj G P.scheme]
  planes : ∀ (A : CommAlgCat.{0} k) (g : affine A ⟶ G) (f : affine A ⟶ P.scheme),
    (P.points A (CartesianMonoidalCategory.lift g f ≫ γ[G,P.scheme])).plane.toSubmodule =
      (P.points A f).plane.toSubmodule.map (D.adjoint A g).toLinearMap
  linearization : LinearizedLineBundles.Linearization G P.scheme P.universal

def overScheme {X : Over (Spec (.of k))} (C : WCover W X) : Over (Spec (.of k)) :=
  Over.mk (C.scheme.hom ≫ X.hom)

def coverProjection {X : Over (Spec (.of k))} (C : WCover W X) : overScheme C ⟶ X :=
  Over.homMk C.scheme.hom rfl

def Incidence (A : CommAlgCat.{0} k) :=
  {z : CentralizerPlane V r A × BorelPlane B A //
    z.fst.plane.toSubmodule ≤ z.snd.plane.toSubmodule}

structure UniversalCover (H : ChevalleyCover (k := k) W) where
  cameral : CameralCover W H P.scheme
  flag : overScheme cameral.cover ⟶ F.scheme
  points : ∀ A : CommAlgCat.{0} k,
    (affine A ⟶ overScheme cameral.cover) ≃ Incidence B A
  centralizer : ∀ (A : CommAlgCat.{0} k) (f : affine A ⟶ overScheme cameral.cover),
    (points A f).val.fst = P.points A (f ≫ coverProjection cameral.cover)
  borel : ∀ (A : CommAlgCat.{0} k) (f : affine A ⟶ overScheme cameral.cover),
    (points A f).val.snd = F.points A (f ≫ flag)
  naturality : ∀ {A A' : CommAlgCat.{0} k} (u : A ⟶ A')
      (f : affine A ⟶ overScheme cameral.cover),
    (points A' (affineMap u ≫ f)).val.fst.plane =
      Module.Grassmannian.map u.hom (points A f).val.fst.plane ∧
    (points A' (affineMap u ≫ f)).val.snd.plane =
      Module.Grassmannian.map u.hom (points A f).val.snd.plane

variable {B P F} {H : ChevalleyCover (k := k) W}
  (C : UniversalCover B P F H)

def centralizerModule : (overScheme C.cameral.cover).left.Modules :=
  (Scheme.Modules.pullback (coverProjection C.cameral.cover).left).obj P.universal

def affineModuleSections {X : Over (Spec (.of k))} (M : X.left.Modules)
    (A : CommAlgCat.{0} k) (f : affine A ⟶ X) : ModuleCat A :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).obj
    ((SheafOfModules.evaluation (Spec (.of A)).ringCatSheaf (.op ⊤)).obj
      ((Scheme.Modules.pullback f.left).obj M))

/-- The global section `m` of the constant module, pulled back to the affine test `f`
(`constantModuleSection`). -/
def constantSection {X : Over (Spec (.of k))} (M : ModuleCat.{0} k) (m : M)
    (A : CommAlgCat.{0} k) (f : affine A ⟶ X) : affineModuleSections (scalarModule X M) A f :=
  constantModuleSection M m f.left

/-- Pulling back a constant module gives the constant module. -/
def scalarPullbackIso {Y Y' : Over (Spec (.of k))} (f : Y' ⟶ Y) (M : ModuleCat.{0} k) :
    (Scheme.Modules.pullback f.left).obj (scalarModule Y M) ≅ scalarModule Y' M :=
  (Scheme.Modules.pullbackComp f.left Y.hom).app ((tilde.functor (.of k)).obj M) ≪≫
    (Scheme.Modules.pullbackCongr f.w).app ((tilde.functor (.of k)).obj M)

/-- The centralizer module of the cover inside its constant Lie algebra module. -/
def centralizerInclusion :
    centralizerModule C ⟶ scalarModule (overScheme C.cameral.cover) (.of k V) :=
  (Scheme.Modules.pullback (coverProjection C.cameral.cover).left).map P.inclusion ≫
    (scalarPullbackIso (coverProjection C.cameral.cover) (.of k V)).hom

structure CartanValueMap where
  quotient : centralizerModule C ⟶
    scalarModule (overScheme C.cameral.cover) (.of k (Fin r → k))
  sourceSections : ∀ (A : CommAlgCat.{0} k) (f : affine A ⟶ overScheme C.cameral.cover),
    affineModuleSections (centralizerModule C) A f ≃ₗ[A]
      (C.points A f).val.fst.plane.toSubmodule
  targetSections : ∀ (A : CommAlgCat.{0} k) (f : affine A ⟶ overScheme C.cameral.cover),
    affineModuleSections (scalarModule (overScheme C.cameral.cover) (.of k (Fin r → k))) A f ≃ₗ[A]
      (Fin r → A)
  /-- The plane identification is the inclusion into the constant Lie algebra module, read in
  the coordinates given by constant sections. -/
  source_ambient : ∀ (A : CommAlgCat.{0} k) (f : affine A ⟶ overScheme C.cameral.cover)
      (x : affineModuleSections (centralizerModule C) A f) (n : ℕ) (a : Fin n → A) (v : Fin n → V),
    (((Scheme.Modules.pullback f.left).map (centralizerInclusion C)).val.app (.op ⊤)).hom x =
        ∑ i, a i • constantSection (.of k V) (v i) A f →
      ((sourceSections A f x : (C.points A f).val.fst.plane.toSubmodule) : LieAt V A) =
        ∑ i, a i ⊗ₜ[k] v i
  /-- The Cartan coordinates are those of the constant sections. -/
  target_constant : ∀ (A : CommAlgCat.{0} k) (f : affine A ⟶ overScheme C.cameral.cover)
      (e : Fin r → k),
    targetSections A f (constantSection (.of k (Fin r → k)) e A f) = fun i => algebraMap k A (e i)
  standardQuotient : ∀ A : CommAlgCat.{0} k, borelAt B A →ₗ[A] (Fin r → A)
  pure : ∀ (A : CommAlgCat.{0} k) (a : A) (b : B.subalgebra) (i : Fin r),
    standardQuotient A
      ⟨a ⊗ₜ[k] b.val, Submodule.tmul_mem_baseChange_of_mem a b.property⟩ i =
        a * algebraMap k A (B.quotient b i)
  normalized : ∀ (A : CommAlgCat.{0} k) (f : affine A ⟶ overScheme C.cameral.cover)
      (g : affine A ⟶ G),
    (C.points A f).val.snd.plane.toSubmodule =
      (borelAt B A).map (D.adjoint A g).toLinearMap →
    ∀ x : affineModuleSections (centralizerModule C) A f,
    ∀ hx : (D.adjoint A g).symm (sourceSections A f x).val ∈ borelAt B A,
      targetSections A f
        ((((Scheme.Modules.pullback f.left).map quotient).val.app (.op ⊤)).hom x) =
          standardQuotient A ⟨(D.adjoint A g).symm (sourceSections A f x).val, hx⟩

end MathlibExt.AlgebraicGeometry.CameralIncidenceModels
