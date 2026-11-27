/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SchubertRankSchemes

/-!
# Actual Bott–Samelson flag towers

The tower begins at the fixed standard coordinate flag. Every step is the
native fibre product of the preceding evaluation with the full-to-partial
projection omitting the changed subspace. Evaluation is its literal second
projection. The final scheme and map are defined before any smoothness,
resolution or fundamental-class theorem is requested.

Source: Brion, math/0410240v1, section 2.2, construction of Z_w and
Proposition 2.2.1. The native scheme fibre-product source is Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BottSamelsonFlagSchemes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GeneralFlagSchemes SchubertRankSchemes PerverseSheaves

abbrev SimpleRoot (n : ℕ) := {i : Fin (n + 1) // 0 < i.val ∧ i.val < n}

def simplePermutation {n : ℕ} (i : SimpleRoot n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨i.val.val - 1, by omega⟩ ⟨i.val.val, i.property.2⟩

def wordPermutation {n : ℕ} (word : List (SimpleRoot n)) : Equiv.Perm (Fin n) :=
  (word.map simplePermutation).prod

/-- A word in the simple reflections is reduced when its product has as many
inversions as the word has letters. -/
def IsReducedWord {n : ℕ} (word : List (SimpleRoot n)) : Prop :=
  length (wordPermutation word) = word.length

structure FlagProjections (n : ℕ) (F : FlagSchemeModel n (fullShape n)) where
  partialFlags : ∀ i : SimpleRoot n, FlagSchemeModel n (omittedShape n i.val)
  projection : ∀ i : SimpleRoot n,
    ForgetMap F (partialFlags i) (Finset.subset_univ _)

abbrev EvaluatedScheme {n : ℕ} (F : FlagSchemeModel n (fullShape n)) :=
  Σ T : ComplexScheme, T ⟶ F.scheme

def towerStep {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    (P : FlagProjections n F) (T : EvaluatedScheme F) (i : SimpleRoot n) : EvaluatedScheme F :=
  let p := (P.projection i).hom
  let f := T.2.left ≫ p.left
  let Z : ComplexScheme := Over.mk (pullback.fst f p.left ≫ T.1.hom)
  ⟨Z, Over.homMk (pullback.snd f p.left) (by
    change pullback.snd f p.left ≫ F.scheme.hom =
      pullback.fst f p.left ≫ T.1.hom
    calc
      _ = pullback.snd f p.left ≫ p.left ≫ (P.partialFlags i).scheme.hom := by rw [Over.w p]
      _ = pullback.fst f p.left ≫ f ≫ (P.partialFlags i).scheme.hom := by
        rw [← Category.assoc, ← pullback.condition, Category.assoc]
      _ = _ := by simp only [f, Category.assoc, Over.w p, Over.w T.2])⟩

def tower {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    (C : CoordinatePoints n F) (P : FlagProjections n F) (word : List (SimpleRoot n)) :
    EvaluatedScheme F :=
  word.foldl (towerStep P) ⟨affineScheme (CommAlgCat.of ℂ ℂ), C.point 1⟩

def bottSamelson {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    (C : CoordinatePoints n F) (P : FlagProjections n F) (word : List (SimpleRoot n)) :
    ComplexScheme := (tower C P word).1

def evaluation {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    (C : CoordinatePoints n F) (P : FlagProjections n F) (word : List (SimpleRoot n)) :
    bottSamelson C P word ⟶ F.scheme := (tower C P word).2

theorem tower_nil {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    (C : CoordinatePoints n F) (P : FlagProjections n F) :
    tower C P [] = ⟨affineScheme (CommAlgCat.of ℂ ℂ), C.point 1⟩ := rfl

theorem tower_append {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    (C : CoordinatePoints n F) (P : FlagProjections n F) (word : List (SimpleRoot n))
    (i : SimpleRoot n) : tower C P (word ++ [i]) = towerStep P (tower C P word) i := by
  simp only [tower, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- These are conclusions about the fixed native tower. The displayed
image equality retains the determinantal Schubert scheme. -/
structure ResolutionProperties {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    (C : CoordinatePoints n F) (P : FlagProjections n F) (word : List (SimpleRoot n))
    (S : SchubertIdealModel F (wordPermutation word) false) : Prop where
  [variety : IsComplexVariety (bottSamelson C P word)]
  [smooth : SmoothOfRelativeDimension word.length (bottSamelson C P word).hom]
  [proper : IsProper (evaluation C P word).left]
  image : (evaluation C P word).left.ker = S.ideal
  isomorphismOnDenseOpen : ∃ U : S.scheme.left.Opens, Dense (U : Set S.scheme.left) ∧
    ∃ f : bottSamelson C P word ⟶ S.scheme,
      f ≫ S.inclusion = evaluation C P word ∧
      IsIso (pullback.snd f.left U.ι)

end MathlibExt.AlgebraicGeometry.BottSamelsonFlagSchemes
