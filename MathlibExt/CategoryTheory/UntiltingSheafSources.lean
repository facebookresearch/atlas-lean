/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.SheafScalarQuotients
public import MathlibExt.CategoryTheory.SheafKernelCompletion
public import MathlibExt.CategoryTheory.SheafWittSource
public import Mathlib.Data.Finset.Range

/-!
# Intrinsic untilting and positive de Rham sheaf sources

The completed positive, tilted, Witt and p-inverted objects below are
the actual native sheaf constructions. Untilting source data fixes sharp
by locally compatible lifts and every finite completion projection.
Fontaine theta is fixed on every Witt vector through its finite Witt
expansion, including the inverse-Frobenius shift.

The local lift clause permits objects without global finite-quotient
lifts. No nonunit or characteristic-p condition is imposed on every
section ring. Empty objects remain in the ambient site.

References: Scholze, arXiv:1205.3463v2, Definition 6.1 and Theorem 6.5;
Mathlib Perfectoid/FontaineTheta.lean and Witt-vector decomposition,
Apache 2.0, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.UntiltingSheafSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open SheafScalarQuotients SheafKernelCompletion SheafWittSource

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{1}] (p : ℕ) [Fact p.Prime]
  (R : Sheaf J CommRingCat.{1})

abbrev positiveCompletion : Sheaf J CommRingCat.{1} :=
  completion R (modP p R) (modPUnit p R)

abbrev positiveProjection (n : ℕ) := projection R (modP p R) (modPUnit p R) n
abbrev positiveModProjection := completedTheta R (modP p R) (modPUnit p R)

abbrev tilt : Sheaf J CommRingCat.{1} := tiltedSource p (modP p R) (modP_zero p R)
abbrev tiltProjection (n : ℕ) := tiltedProjection p (modP p R) (modP_zero p R) n

abbrev inverseFrobenius : End (tilt p R) :=
  End.of (inverseEndShift (modP p R) (End.of (frobeniusSheaf p (modP p R) (modP_zero p R))))

abbrev inf : Sheaf J CommRingCat.{1} := wittSheaf p (tilt p R)
abbrev rationalInf : Sheaf J CommRingCat.{1} := localizeP p (inf p R)
abbrev completedRegular : Sheaf J CommRingCat.{1} := localizeP p (positiveCompletion p R)

/-- Primitive untilting is pinned to actual local lifts and all finite Witt coordinates. -/
structure UntiltingData where
  sharp : ∀ U : Cᵒᵖ, (tilt p R).obj.obj U → (positiveCompletion p R).obj.obj U
  sharp_natural : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : (tilt p R).obj.obj U),
    sharp V (((tilt p R).obj.map f).hom x) =
      ((positiveCompletion p R).obj.map f).hom (sharp U x)
  sharp_zero : ∀ U, sharp U 0 = 0
  sharp_one : ∀ U, sharp U 1 = 1
  sharp_mul : ∀ U x y, sharp U (x * y) = sharp U x * sharp U y
  local_lifts : ∀ (U : Cᵒᵖ) (x : (tilt p R).obj.obj U),
    ∃ S : Sieve U.unop, S ∈ J U.unop ∧
      ∀ (V : C) (f : V ⟶ U.unop), S f →
        ∃ a : ℕ → (positiveCompletion p R).obj.obj (op V),
          ∀ n : ℕ, ((positiveModProjection p R).hom.app (op V)).hom (a n) =
            ((tiltProjection p R n).hom.app (op V)).hom
              (((tilt p R).obj.map f.op).hom x)
  sharp_source : ∀ (U : Cᵒᵖ) (x : (tilt p R).obj.obj U)
      (a : ℕ → (positiveCompletion p R).obj.obj U),
    (∀ n : ℕ, ((positiveModProjection p R).hom.app U).hom (a n) =
      ((tiltProjection p R n).hom.app U).hom x) →
    ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((positiveProjection p R m).hom.app U).hom (sharp U x) =
        ((positiveProjection p R m).hom.app U).hom (a n ^ p ^ n)
  theta : inf p R ⟶ positiveCompletion p R
  theta_source : ∀ (U : Cᵒᵖ) (w : WittVector p ((tilt p R).obj.obj U)) (n : ℕ),
    ((positiveProjection p R n).hom.app U).hom
      (((theta.hom.app U).hom)
        (((toSheafify J (wittPresheaf p (tilt p R))).app U).hom w)) =
    ((positiveProjection p R n).hom.app U).hom
      (∑ i ∈ Finset.range (n + 1), (p : (positiveCompletion p R).obj.obj U) ^ i *
        sharp U ((((inverseFrobenius p R) ^ i).asHom.hom.app U).hom (w.coeff i)))

namespace UntiltingData

variable (A : UntiltingData p R)

/-- p-inverted theta is the actual map of the two native localization coproducts. -/
def rationalTheta : rationalInf p R ⟶ completedRegular p R :=
  coprod.desc (A.theta ≫ localizePUnit p (positiveCompletion p R)) coprod.inr

abbrev deRhamPositive : Sheaf J CommRingCat.{1} :=
  completion (rationalInf p R) (completedRegular p R) A.rationalTheta

abbrev completedTheta : A.deRhamPositive ⟶ completedRegular p R :=
  SheafKernelCompletion.completedTheta
    (rationalInf p R) (completedRegular p R) A.rationalTheta

/-- The actual kernel of the completed finite quotient projection. -/
def positiveFiltration (n : ℕ) (U : Cᵒᵖ) : Ideal (A.deRhamPositive.obj.obj U) :=
  match n with
  | 0 => ⊤
  | n + 1 => RingHom.ker
      ((projection (rationalInf p R) (completedRegular p R) A.rationalTheta n).hom.app U).hom

end UntiltingData

end MathlibExt.CategoryTheory.UntiltingSheafSources
