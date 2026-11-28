/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Actual path maps at fixed original labels

An original map of arrow families extends to all complete native paths.
Identity, composition and every original generator are retained. Actual
injectivity on each arrow family gives injectivity on full paths, with
independent object, source-arrow and target-arrow universes.
-/

universe u v w
open CategoryTheory

namespace CategoryTheory.FixedLabelPathMaps

variable {O : Type u} (Q : Quiver.{v} O) (R : Quiver.{w} O)
  (m : ∀ {a b : O}, Q.Hom a b → R.Hom a b)

/-- The actual arrow map with the same individual original labels. -/
def prefunctor : @Prefunctor O Q O R :=
  @Prefunctor.mk O Q O R (fun a => a) m

/-- Map every complete original path by its actual arrow maps. -/
def mapPath {a b : O} (p : @Quiver.Path O Q a b) : @Quiver.Path O R a b :=
  @Prefunctor.mapPath O Q O R (prefunctor Q R m) a b p

/-- The empty original path remains the same empty path. -/
theorem mapPath_nil (a : O) :
    mapPath Q R m (@Quiver.Path.nil O Q a) = @Quiver.Path.nil O R a := rfl

/-- A complete path followed by an original arrow retains the full same cons. -/
theorem mapPath_cons {a b c : O} (p : @Quiver.Path O Q a b) (e : Q.Hom b c) :
    mapPath Q R m (@Quiver.Path.cons O Q a b c p e) =
      @Quiver.Path.cons O R a b c (mapPath Q R m p) (m e) := rfl

/-- The actual map retains every original singleton path. -/
theorem mapPath_single {a b : O} (e : Q.Hom a b) :
    mapPath Q R m (@Quiver.Hom.toPath O Q a b e) = @Quiver.Hom.toPath O R a b (m e) := rfl

/-- Every complete path concatenation is preserved by the actual arrow map. -/
theorem mapPath_comp {a b c : O} (p : @Quiver.Path O Q a b) (q : @Quiver.Path O Q b c) :
    mapPath Q R m (@Quiver.Path.comp O Q a b c p q) =
      @Quiver.Path.comp O R a b c (mapPath Q R m p) (mapPath Q R m q) :=
  @Prefunctor.mapPath_comp O Q O R (prefunctor Q R m) a b p c q

variable (hm : ∀ a b, Function.Injective (@m a b))

include hm in
/-- Actual injection of every original arrow gives injection of complete native paths. -/
theorem mapPath_injective (a b : O) : Function.Injective (@mapPath O Q R m a b) := by
  intro p q h
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e => cases h
  | cons p e ih =>
      cases q with
      | nil => cases h
      | cons q f =>
          change (mapPath Q R m p).cons (m e) = (mapPath Q R m q).cons (m f) at h
          obtain ⟨rfl, hp, he⟩ := Quiver.Path.cons.inj h
          have he' := hm _ _ (eq_of_heq he)
          obtain rfl := he'
          exact congrArg (fun p => @Quiver.Path.cons O Q _ _ _ p e) (ih (eq_of_heq hp))

end CategoryTheory.FixedLabelPathMaps
