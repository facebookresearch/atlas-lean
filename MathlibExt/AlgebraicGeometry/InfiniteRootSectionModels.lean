/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CartesianStackTensorComparisons
public import MathlibExt.AlgebraicGeometry.FiniteRootTowers
public import MathlibExt.AlgebraicGeometry.SchemeStackModuleModels

/-!
# Infinite roots on the whole fibred stack

Line objects and sections are actual cartesian O-modules. Tensor words,
section powers and all reassociations are native monoidal operations.
The first line is fixed on every affine family to the pullback of an
actual base line-with-section. All power comparisons preserve sections
and their native unit/composition diagrams.

Geometric nonvanishing is tested on every affine scheme family over the
geometric field, including nonreduced families. It is not a nonvanishing
test on field-valued points. This is the entire geometric-fibre condition
of Talpo--Vistoli arXiv:1410.1164v2, Definition5.1(d).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.InfiniteRootSectionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry _root_.AlgebraicGeometry.StackAffineModules
open _root_.AlgebraicGeometry.CartesianStackModules
open _root_.AlgebraicGeometry.CartesianStackTensorProducts
open DeligneFaltingsCategories FiniteRootTowers ModuleTensorPullbackSections

variable {S : Scheme.{0}} (R : Stack S)

/-- Instance adapter of the already fixed native cartesian tensor landing. -/
class HasTensorLanding : Prop where
  landing : TensorLanding R

theorem tensorLandingData (T : TensorLanding R) : HasTensorLanding R := ⟨T⟩

variable [T : HasTensorLanding R]

local instance nativeMonoidal : MonoidalCategory (QCoh R) :=
  CartesianStackTensorComparisons.monoidal R T.landing

def tensorPower (L : QCoh R) : ℕ → QCoh R
  | 0 => structureModule R
  | n + 1 => tensorPower L n ⊗ L

def tensorPowerMap {L M : QCoh R} (f : L ⟶ M) :
    (n : ℕ) → tensorPower R L n ⟶ tensorPower R M n
  | 0 => 𝟙 (structureModule R)
  | n + 1 => tensorPowerMap f n ⊗ₘ f

def sectionPower {L : QCoh R} (s : structureModule R ⟶ L) :
    (n : ℕ) → structureModule R ⟶ tensorPower R L n
  | 0 => 𝟙 (structureModule R)
  | n + 1 => (λ_ (structureModule R)).inv ≫ (sectionPower s n ⊗ₘ s)

/-- Native reassociation and unitors, retaining the actual tensor word. -/
def appendIso (L : QCoh R) (n : ℕ) : (m : ℕ) →
    tensorPower R L n ⊗ tensorPower R L m ≅ tensorPower R L (n + m)
  | 0 => ρ_ (tensorPower R L n)
  | m + 1 => (α_ (tensorPower R L n) (tensorPower R L m) L).symm ≪≫
      (appendIso L n m ⊗ᵢ Iso.refl L)

def iterationIso (L : QCoh R) (n : ℕ) : (m : ℕ) →
    tensorPower R (tensorPower R L n) m ≅ tensorPower R L (n * m)
  | 0 => Iso.refl (structureModule R)
  | m + 1 => (iterationIso L n m ⊗ᵢ Iso.refl (tensorPower R L n)) ≪≫
      appendIso R L (n * m) n ≪≫
        eqToIso (congrArg (tensorPower R L) (Nat.mul_succ n m).symm)

/-- Rank one uses local bases of the actual localized coefficient module. -/
def IsLine (L : QCoh R) : Prop :=
  ∀ a : AffinePoint R,
    Module.FinitePresentation ((rings R).obj (op a)) (L.obj.obj (op a)) ∧
    ∀ q : PrimeSpectrum ((rings R).obj (op a)),
      ∃ f : (rings R).obj (op a), f ∉ q.asIdeal ∧
        Nonempty (Module.Basis (Fin 1) (Localization.Away f)
          (LocalizedModule (Submonoid.powers f) (L.obj.obj (op a))))

/-- Whole geometric-fibre nonzero section: all scheme families, not only fields. -/
def GeometricNonzero {Ω : Type} [Field Ω] (x : Spec (.of Ω) ⟶ S)
    {L : QCoh R} (s : structureModule R ⟶ L) : Prop :=
  ∃ (a : AffinePoint R) (scalar : a.obj.base.left ⟶ Spec (.of Ω)),
    scalar ≫ x = a.obj.base.hom ∧ s.hom.app (op a) (1 : (rings R).obj (op a)) ≠ 0

/-- Native restriction of an actually pulled base-module section. -/
def baseRestriction (L : S.Modules) {a b : AffinePoint R} (h : a ⟶ b)
    (s : Γ((Scheme.Modules.pullback b.obj.base.hom).obj L, ⊤)) :
    Γ((Scheme.Modules.pullback a.obj.base.hom).obj L, ⊤) :=
  let t := localPullback h.hom.base.left ((Scheme.Modules.pullback b.obj.base.hom).obj L) ⊤ s
  let v := ((Scheme.Modules.pullbackComp h.hom.base.left b.obj.base.hom).hom.app L).val.app
    (op (⊤ : a.obj.base.left.Opens))
  let e := eqToHom (congrArg (fun f => (Scheme.Modules.pullback f).obj L) (Over.w h.hom.base))
  (e.val.app (op (⊤ : a.obj.base.left.Opens))).hom (v.hom t)

theorem ratioMultiply (l m n : Exponent) (hlm : l.val ∣ m.val) (hmn : m.val ∣ n.val) :
    (n.val / m.val) * (m.val / l.val) = n.val / l.val := by
  rw [← Nat.mul_div_assoc _ hlm]
  congr 1
  exact (Nat.mul_comm _ _).trans (Nat.mul_div_cancel' hmn)

def selfPowerIso (L : QCoh R) (n : Exponent) : tensorPower R L (n.val / n.val) ≅ L :=
  eqToIso (congrArg (tensorPower R L) (Nat.div_self n.property)) ≪≫ λ_ L

/-- Definition5.1 with literal modules, sections and all transition coherences. -/
structure InfiniteRoot where
  line : Exponent → QCoh R
  isLine : ∀ n, IsLine R (line n)
  sectionMap : ∀ n, structureModule R ⟶ line n
  transition : ∀ (m n : Exponent) (_h : m.val ∣ n.val),
    tensorPower R (line n) (n.val / m.val) ≅ line m
  sections : ∀ (m n : Exponent) (h : m.val ∣ n.val),
    sectionPower R (sectionMap n) (n.val / m.val) ≫ (transition m n h).hom = sectionMap m
  identity : ∀ n, transition n n (dvd_refl _) = selfPowerIso R (line n) n
  composition : ∀ (l m n : Exponent) (hlm : l.val ∣ m.val) (hmn : m.val ∣ n.val),
    (transition l n (dvd_trans hlm hmn)).hom =
      eqToHom (congrArg (tensorPower R (line n)) (ratioMultiply l m n hlm hmn).symm) ≫
        (iterationIso R (line n) (n.val / m.val) (m.val / l.val)).inv ≫
          tensorPowerMap R (transition m n hmn).hom (m.val / l.val) ≫
            (transition l m hlm).hom
  baseLine : DivisorObject S
  baseSections : ∀ a : AffinePoint R,
    (line ⟨1, by omega⟩).obj.obj (op a) ≃ₗ[Γ(a.obj.base.left, ⊤)]
      Γ((Scheme.Modules.pullback a.obj.base.hom).obj baseLine.module, ⊤)
  base_naturality : ∀ {a b : AffinePoint R} (h : a ⟶ b)
      (s : (line ⟨1, by omega⟩).obj.obj (op b)),
    baseSections a ((line ⟨1, by omega⟩).obj.map h.op s) =
      baseRestriction R baseLine.module h (baseSections b s)
  base_section : ∀ a : AffinePoint R,
    baseSections a ((sectionMap ⟨1, by omega⟩).hom.app (op a) (1 : (rings R).obj (op a))) =
      (((LineBundleTaskContracts.pullbackSection a.obj.base.hom baseLine.sectionMap).val.app
        (op (⊤ : a.obj.base.left.Opens))).hom (1 : Γ(a.obj.base.left, ⊤)))
  geometric : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
    ∃ N : Exponent, ∀ n : Exponent, N.val ∣ n.val → GeometricNonzero R x (sectionMap n)

end MathlibExt.AlgebraicGeometry.InfiniteRootSectionModels
