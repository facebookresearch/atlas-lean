/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Grassmannian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.PerverseSheaves
public import MathlibExt.AlgebraicGeometry.ProjectiveDirectImage

/-!
# All-rank flag schemes with their actual affine points

An affine flag is a nested family of actual submodules of the native scalar
extension of C^n. Each quotient is the native finite projective Grassmannian
quotient, with its rank at every prime. A representing model is normalized
on every complex algebra, including nonreduced algebras, and on every algebra
map by the native Grassmannian base change. Its scheme maps cannot be chosen
independently of their effects on these flags.

Source: Michel Brion, *Lectures on the geometry of flag varieties*,
math/0410240v1, sections 1.1–1.2. Native quotient/base-change definitions are
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
RingTheory/Grassmannian.lean (Kenny Lau, 2025, Apache 2.0). This adaptation
adds nested submodules, partial ranks and representing-scheme normalization;
it does not substitute quotient rank d for the source's subspace rank d.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralFlagSchemes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open PerverseSheaves Opposite
open scoped TensorProduct

abbrev Shape (n : ℕ) := Finset (Fin (n + 1))
abbrev Step {n : ℕ} (D : Shape n) := {d : Fin (n + 1) // d ∈ D}

def fullShape (n : ℕ) : Shape n := Finset.univ
def omittedShape (n : ℕ) (i : Fin (n + 1)) : Shape n := (fullShape n).erase i

abbrev CoordinateSpace (n : ℕ) := Fin n → ℂ
abbrev ExtendedSpace (A : CommAlgCat.{0} ℂ) (n : ℕ) := A ⊗[ℂ] CoordinateSpace n

structure AffineFlag (A : CommAlgCat.{0} ℂ) (n : ℕ) (D : Shape n) where
  term : ∀ d : Step D, Module.Grassmannian A (ExtendedSpace A n) (n - d.val.val)
  nested : ∀ d e : Step D, d.val ≤ e.val →
    (term d).toSubmodule ≤ (term e).toSubmodule
  zero : ∀ d : Step D, d.val.val = 0 → (term d).toSubmodule = ⊥
  top : ∀ d : Step D, d.val.val = n → (term d).toSubmodule = ⊤

def AffineFlag.forget {A : CommAlgCat.{0} ℂ} {n : ℕ} {D E : Shape n}
    (F : AffineFlag A n D) (h : E ⊆ D) : AffineFlag A n E where
  term d := F.term ⟨d.val, h d.property⟩
  nested _ _ hd := F.nested _ _ hd
  zero _ hd := F.zero _ hd
  top _ hd := F.top _ hd

theorem AffineFlag.forget_term {A : CommAlgCat.{0} ℂ} {n : ℕ} {D E : Shape n}
    (F : AffineFlag A n D) (h : E ⊆ D) (d : Step E) :
    (F.forget h).term d = F.term ⟨d.val, h d.property⟩ := rfl

/-- Actual affine complex scheme, with its specified scalar structure map. -/
def affineScheme (A : CommAlgCat.{0} ℂ) : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

instance affineScheme_isAffine (A : CommAlgCat.{0} ℂ) : IsAffine (affineScheme A).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

def affineMap {A B : CommAlgCat.{0} ℂ} (f : A ⟶ B) : affineScheme B ⟶ affineScheme A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) (by
    simp only [affineScheme, Over.mk_hom, ← Spec.map_comp]
    congr 1
    ext a
    exact f.hom.commutes a)

def normalizedShape {n : ℕ} (D : Shape n) : Shape n :=
  insert 0 (insert (Fin.last n) D)

def blockSize {n : ℕ} (D : Shape n) (d : Fin (n + 1)) : ℕ :=
  d.val - ((normalizedShape D).filter (· < d)).sup Fin.val

/-- Partial ranks have implicit endpoints 0 and n. The final complement
block n-max(D) contributes even when n is not an explicit selected rank. -/
def flagDimension {n : ℕ} (D : Shape n) : ℕ :=
  ∑ d ∈ normalizedShape D, ∑ e ∈ normalizedShape D,
    if d < e then blockSize D d * blockSize D e else 0

/-- A model of the actual flag functor. Representability and geometry are
construction targets; no flag-scheme theorem is a standing assumption. -/
structure FlagSchemeModel (n : ℕ) (D : Shape n) where
  scheme : ComplexScheme
  [variety : IsComplexVariety scheme]
  [proper : IsProper scheme.hom]
  [smooth : SmoothOfRelativeDimension (flagDimension D) scheme.hom]
  projective : ProjectiveSpace.IsProjective scheme
  points : ∀ A : CommAlgCat.{0} ℂ, (affineScheme A ⟶ scheme) ≃ AffineFlag A n D
  baseChange : ∀ {A B : CommAlgCat.{0} ℂ} (f : A ⟶ B)
    (x : affineScheme A ⟶ scheme) (d : Step D),
    (points B (affineMap f ≫ x)).term d = Module.Grassmannian.map f.hom ((points A x).term d)

attribute [instance] FlagSchemeModel.variety FlagSchemeModel.proper FlagSchemeModel.smooth

/-- A partial projection is the actual scheme map which forgets the selected
steps on every affine test scheme. -/
structure ForgetMap {n : ℕ} {D E : Shape n} (F : FlagSchemeModel n D)
    (P : FlagSchemeModel n E) (h : E ⊆ D) where
  hom : F.scheme ⟶ P.scheme
  points : ∀ (A : CommAlgCat.{0} ℂ) (x : affineScheme A ⟶ F.scheme),
    P.points A (x ≫ hom) = (F.points A x).forget h

/-- Coordinate flags use actual standard basis tensors. -/
def coordinateSubmodule (A : CommAlgCat.{0} ℂ) (n : ℕ)
    (w : Equiv.Perm (Fin n)) (d : Fin (n + 1)) : Submodule A (ExtendedSpace A n) :=
  Submodule.span A {v | ∃ i : Fin n, i.val < d.val ∧
    v = TensorProduct.tmul ℂ (1 : A) (Pi.single (w i) 1)}

structure CoordinatePoints (n : ℕ) (F : FlagSchemeModel n (fullShape n)) where
  point : Equiv.Perm (Fin n) → (affineScheme (CommAlgCat.of ℂ ℂ) ⟶ F.scheme)
  normalization : ∀ w d,
    ((F.points _ (point w)).term d).toSubmodule = coordinateSubmodule _ n w d.val

/-- The adjacent correspondence is the actual fibre product over the partial
flag which omits the changed subspace, not a flag-equality predicate. -/
def adjacent {n : ℕ} (F : FlagSchemeModel n (fullShape n)) (i : Fin (n + 1))
    (P : FlagSchemeModel n (omittedShape n i))
    (p : ForgetMap F P (Finset.subset_univ _)) : ComplexScheme :=
  Over.mk (pullback.fst p.hom.left p.hom.left ≫ F.scheme.hom)

def adjacentLeft {n : ℕ} (F : FlagSchemeModel n (fullShape n)) (i : Fin (n + 1))
    (P : FlagSchemeModel n (omittedShape n i))
    (p : ForgetMap F P (Finset.subset_univ _)) : adjacent F i P p ⟶ F.scheme :=
  Over.homMk (pullback.fst p.hom.left p.hom.left) rfl

def adjacentRight {n : ℕ} (F : FlagSchemeModel n (fullShape n)) (i : Fin (n + 1))
    (P : FlagSchemeModel n (omittedShape n i))
    (p : ForgetMap F P (Finset.subset_univ _)) : adjacent F i P p ⟶ F.scheme :=
  Over.homMk (pullback.snd p.hom.left p.hom.left) (by
    change pullback.snd p.hom.left p.hom.left ≫ F.scheme.hom =
      pullback.fst p.hom.left p.hom.left ≫ F.scheme.hom
    rw [← Over.w p.hom]
    rw [← Category.assoc, ← Category.assoc, pullback.condition])

end MathlibExt.AlgebraicGeometry.GeneralFlagSchemes
