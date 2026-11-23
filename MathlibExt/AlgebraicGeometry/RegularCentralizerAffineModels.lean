/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.RingTheory.Grassmannian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import MathlibExt.AlgebraicGeometry.CameralTorusBands
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison

/-!
# Actual regular-centralizer planes and their native parameter scheme

The affine r-plane is the actual submodule in the native quotient
Grassmannian with quotient rank dim(g)-r. A regular section has its
actual ad-kernel as that plane and locally projective ad-cokernel of
rank r; this retains geometric regularity under nonflat specialization.
A regular-centralizer plane is abelian and etale-locally such a kernel.
The represented parameter scheme uses this full functor on all affine
algebras, including its literal Grassmannian base changes.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections1--2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RegularCentralizerAffineModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {k : Type} [Field k] (V : Type) [LieRing V] [LieAlgebra k V] [FiniteDimensional k V]
  (r : ℕ) (A : CommAlgCat.{0} k)

abbrev LieAt := A ⊗[k] V

def ad (x : LieAt V A) : LieAt V A →ₗ[A] LieAt V A := LieAlgebra.ad A (LieAt V A) x

def centralizer (x : LieAt V A) : Submodule A (LieAt V A) := LinearMap.ker (ad V A x)

abbrev Plane := Module.Grassmannian A (LieAt V A) (Module.finrank k V - r)

structure RegularElement where
  value : LieAt V A
  plane : Plane V r A
  kernel : plane.toSubmodule = centralizer V A value
  [finiteCokernel : Module.Finite A ((LieAt V A) ⧸ LinearMap.range (ad V A value))]
  [projectiveCokernel : Module.Projective A ((LieAt V A) ⧸ LinearMap.range (ad V A value))]
  cokernelRank : ∀ p : PrimeSpectrum A,
    Module.rankAtStalk (R := A) ((LieAt V A) ⧸ LinearMap.range (ad V A value)) p = r

attribute [instance] RegularElement.finiteCokernel RegularElement.projectiveCokernel

structure LocalRegularPresentation (P : Plane V r A) (p : PrimeSpectrum A) where
  algebra : CommAlgCat.{0} k
  map : A ⟶ algebra
  etale : Etale (Spec.map (CommRingCat.ofHom map.hom.toRingHom))
  point : PrimeSpectrum algebra
  point_eq : PrimeSpectrum.comap map.hom.toRingHom point = p
  regular : RegularElement V r algebra
  plane : (Module.Grassmannian.map map.hom P).toSubmodule = regular.plane.toSubmodule

structure CentralizerPlane where
  plane : Plane V r A
  abelian : ∀ x : LieAt V A, x ∈ plane.toSubmodule →
    ∀ y : LieAt V A, y ∈ plane.toSubmodule → ⁅x, y⁆ = 0
  presentations : ∀ p : PrimeSpectrum A, Nonempty (LocalRegularPresentation V r A plane p)

omit [FiniteDimensional k V] in
@[ext] theorem CentralizerPlane.ext (P Q : CentralizerPlane V r A)
    (h : P.plane = Q.plane) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

def ofRegular (x : RegularElement V r A)
    (abelian : ∀ a : LieAt V A, a ∈ centralizer V A x.value →
      ∀ b : LieAt V A, b ∈ centralizer V A x.value → ⁅a, b⁆ = 0)
    (presentations : ∀ p : PrimeSpectrum A, Nonempty (LocalRegularPresentation V r A x.plane p)) :
    CentralizerPlane V r A where
  plane := x.plane
  abelian := by simpa only [x.kernel] using abelian
  presentations := presentations

structure BaseChange {A B : CommAlgCat.{0} k} (f : A ⟶ B) (P : CentralizerPlane V r A) where
  plane : CentralizerPlane V r B
  normalized : plane.plane = Module.Grassmannian.map f.hom P.plane

def lieModule (X : Over (Spec (.of k))) : X.left.Modules :=
  (Scheme.Modules.pullback X.hom).obj ((tilde.functor (.of k)).obj (ModuleCat.of k V))

/-- The global section `m` of the constant module `M`, pulled back along `X.hom` and then along
`f`: the units of the pullback-pushforward adjunctions applied to the section of `M^~` over
`Spec k` given by `m`. -/
def constantModuleSection {X : Over (Spec (.of k))} (M : ModuleCat.{0} k) (m : M)
    {Y : Scheme.{0}} (f : Y ⟶ X.left) :
    Γ((Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback X.hom).obj ((tilde.functor (.of k)).obj M)), ⊤) :=
  let s : ((tilde.functor (.of k)).obj M).val.obj (.op ⊤) := (tilde.isoTop (R := .of k) M).hom m
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((Scheme.Modules.pullback X.hom).obj ((tilde.functor (.of k)).obj M))).val.app (.op ⊤)).hom
    ((((Scheme.Modules.pullbackPushforwardAdjunction X.hom).unit.app
      ((tilde.functor (.of k)).obj M)).val.app (.op ⊤)).hom s)

structure ParameterScheme where
  scheme : Over (Spec (.of k))
  universal : scheme.left.Modules
  rank : CurveVectorBundles.IsVectorBundle universal r
  inclusion : universal ⟶ lieModule V scheme
  [mono : Mono inclusion]
  points : ∀ A : CommAlgCat.{0} k,
    (Over.mk (Spec.algebraMap k A) ⟶ scheme) ≃ CentralizerPlane V r A
  reindex : ∀ {A B : CommAlgCat.{0} k} (f : A ⟶ B) (P : CentralizerPlane V r A), BaseChange V r f P
  naturality : ∀ {A B : CommAlgCat.{0} k} (f : A ⟶ B)
      (g : Over.mk (Spec.algebraMap k A) ⟶ scheme),
    points B ((Over.homMk (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) =
          Spec.map (CommRingCat.ofHom (algebraMap k B))
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact f.hom.commutes x) : Over.mk (Spec.algebraMap k B) ⟶
        Over.mk (Spec.algebraMap k A)) ≫ g) =
      (reindex f (points A g)).plane
  sectionModule : ∀ (A : CommAlgCat.{0} k) (f : Over.mk (Spec.algebraMap k A) ⟶ scheme),
    letI : Module A Γ((Scheme.Modules.pullback f.left).obj universal, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso (.of A)).inv.hom
    Γ((Scheme.Modules.pullback f.left).obj universal, ⊤) ≃ₗ[A] (points A f).plane.toSubmodule
  lieSections : ∀ (A : CommAlgCat.{0} k) (f : Over.mk (Spec.algebraMap k A) ⟶ scheme),
    letI : Module A Γ((Scheme.Modules.pullback f.left).obj (lieModule V scheme), ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso (.of A)).inv.hom
    Γ((Scheme.Modules.pullback f.left).obj (lieModule V scheme), ⊤) ≃ₗ[A] LieAt V A
  /-- The Lie algebra coordinates send the pullback of each constant section `v` to `1 ⊗ v`;
  as these sections generate, this fixes `lieSections`, and `inclusion_sections` then fixes
  `sectionModule`. -/
  lieSections_constant : ∀ (A : CommAlgCat.{0} k) (f : Over.mk (Spec.algebraMap k A) ⟶ scheme)
      (v : V),
    lieSections A f (constantModuleSection (.of k V) v f.left) = (1 : A) ⊗ₜ[k] v
  inclusion_sections : ∀ (A : CommAlgCat.{0} k) (f : Over.mk (Spec.algebraMap k A) ⟶ scheme)
    (s : Γ((Scheme.Modules.pullback f.left).obj universal, ⊤)),
    lieSections A f ((((Scheme.Modules.pullback f.left).map inclusion).val.app (.op ⊤)).hom s) =
      (sectionModule A f s).val

end MathlibExt.AlgebraicGeometry.RegularCentralizerAffineModels
