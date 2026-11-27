/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.FixedLabelPathMaps

/-!
# The original quiver dictionary and its full Hom-family readback

Reading the entire original arrow family and rebuilding its one-field
quiver dictionary recovers that same dictionary. Complete paths transfer
through that equality with both inverse maps and literal singleton,
identity and composition readbacks.
-/

universe u v
open CategoryTheory
namespace CategoryTheory.FixedLabelPathMaps
variable {O : Type u} (Q : Quiver.{v} O)

/-- The entire original Hom family recovers its same one-field quiver dictionary. -/
theorem quiver_eta : (Quiver.mk Q.Hom : Quiver.{v} O) = Q := by
  cases Q
  rfl

/-- Transfer a complete path from the actual Hom-family dictionary to its same original
dictionary. -/
def fromHomDictionary {a b : O} (p : @Quiver.Path O (Quiver.mk Q.Hom) a b) : @Quiver.Path O Q a b :=
  (quiver_eta Q) ▸ p

/-- Transfer back to the actual full Hom-family dictionary. -/
def toHomDictionary {a b : O} (p : @Quiver.Path O Q a b) : @Quiver.Path O (Quiver.mk Q.Hom) a b :=
  (quiver_eta Q).symm ▸ p

/-- The actual original full path is recovered by both dictionary maps. -/
theorem from_toHomDictionary {a b : O} (p : @Quiver.Path O Q a b) :
    fromHomDictionary Q (toHomDictionary Q p) = p := by
  cases Q
  rfl

/-- The actual full Hom-family path is recovered by both dictionary maps. -/
theorem to_fromHomDictionary {a b : O} (p : @Quiver.Path O (Quiver.mk Q.Hom) a b) :
    toHomDictionary Q (fromHomDictionary Q p) = p := by
  cases Q
  rfl

/-- Singleton arrows are their same full original arrow paths under the dictionary map. -/
theorem fromHomDictionary_single {a b : O} (e : Q.Hom a b) :
    fromHomDictionary Q (@Quiver.Hom.toPath O (Quiver.mk Q.Hom) a b e) =
      @Quiver.Hom.toPath O Q a b e := by
  cases Q
  rfl


/-- Empty paths retain their same original identity under the dictionary map. -/
theorem fromHomDictionary_nil (a : O) :
    fromHomDictionary Q (@Quiver.Path.nil O (Quiver.mk Q.Hom) a) = @Quiver.Path.nil O Q a := by
  cases Q
  rfl

/-- Full original path composition is retained under the dictionary map. -/
theorem fromHomDictionary_comp {a b c : O}
    (p : @Quiver.Path O (Quiver.mk Q.Hom) a b) (r : @Quiver.Path O (Quiver.mk Q.Hom) b c) :
    fromHomDictionary Q (@Quiver.Path.comp O (Quiver.mk Q.Hom) a b c p r) =
      @Quiver.Path.comp O Q a b c (fromHomDictionary Q p) (fromHomDictionary Q r) := by
  cases Q
  rfl

variable (R : Quiver.{v} O) (m : ∀ {a b : O}, Q.Hom a b → R.Hom a b)

/-- Both dictionary readbacks retain the same original full map on paths. -/
theorem fromHomDictionary_map {a b : O} (p : @Quiver.Path O (Quiver.mk Q.Hom) a b) :
    fromHomDictionary R
      (FixedLabelPathMaps.mapPath (Quiver.mk Q.Hom) (Quiver.mk R.Hom) m p) =
      FixedLabelPathMaps.mapPath Q R m (fromHomDictionary Q p) := by
  cases Q
  cases R
  rfl

end CategoryTheory.FixedLabelPathMaps
