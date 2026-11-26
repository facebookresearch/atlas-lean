/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamily

/-!
# Exact endpoint transport of last-interval families

Transport changes only the supplied equality labels of the 
source and target. The constructed enriched simplex and all its
Hom maps agree, with no quotient of objects or supplied
comparison outcome.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomFrontFamilyTransport
open SimplicialEnrichment HomFrontFamily
variable {C : Carrier.{u}} {n : ℕ} {x y x' y' : C}

/-- Equality of all last-interval maps determines the same family. -/
theorem family_ext {P Q : Family x y n} (h : ∀ i, P.map i = Q.map i) : P = Q := by
  cases P with
  | mk f hf =>
    cases Q with
    | mk g hg =>
      have he : f = g := funext h
      subst g
      rfl

/-- Retarget each last-interval map along the two specified object equalities. -/
def retarget (hx : x = x') (hy : y = y') (P : Family x y n) : Family x' y' n where
  map i := P.map i ≫ EqualityTransport.hom hx hy
  map_comp i j q p r := congrArg ((EqualityTransport.hom hx hy).app q) (P.map_comp i j q p r)

/-- Reflexive endpoint transport recovers every interval map exactly. -/
theorem retarget_refl (P : Family x y n) : retarget rfl rfl P = P :=
  family_ext (fun i => Category.comp_id (P.map i))

/-- The enriched simplex is unchanged by the two supplied endpoint equality
transports. -/
theorem simplex_retarget (hx : x = x') (hy : y = y') (P : Family x y n) :
    simplex x y P = simplex x' y' (retarget hx hy P) := by
  subst x'
  subst y'
  exact congrArg (simplex x y) (retarget_refl P).symm

end CategoryTheory.CoherentRealization.HomFrontFamilyTransport
