/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.CategoryTheory.NatIso
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerData
public import MathlibExt.AlgebraicTopology.SingularHomology.EilenbergSteenrod

/-! # Integer-graded homotopy invariance -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TopPair.HomotopyEquiv

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X Y : TopPair.{w}}

open AlgebraicTopology

/-- Pair-homotopic maps induce equal maps on integer-graded relative homology. -/
theorem relativeSingularHomologyIntFunctor_map_eq_of_homotopy
    (R : C) {f g : X ⟶ Y} (H : Homotopy f g) (z : ℤ) :
    (relativeSingularHomologyIntFunctor C R z).map f =
      (relativeSingularHomologyIntFunctor C R z).map g := by
  by_cases h : 0 ≤ z
  · have hz_eq : z = ((z.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h).symm
    rw [hz_eq]
    exact (NatIso.map_eq_iff
      (relativeSingularHomologyNatToIntIso C R z.toNat) f g).mpr
        (relativeSingularHomologyFunctor_map_eq_of_homotopy R H z.toNat)
  · have hz : z < 0 := lt_of_not_ge h
    have hX : IsZero ((relativeSingularHomologyIntFunctor C R z).obj X) :=
      isZero_relativeSingularHomologyIntFunctor_of_neg C R z hz X
    exact IsZero.eq_of_src hX _ _

end TopPair.HomotopyEquiv

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

noncomputable instance singularHomologyIntData_isHomotopyInvariant (R : C) :
    (singularHomologyIntData C R).IsHomotopyInvariant where
  map_eq_of_homotopy H z := by
    change (relativeSingularHomologyIntFunctor C R z).map _ =
      (relativeSingularHomologyIntFunctor C R z).map _
    exact
      TopPair.HomotopyEquiv.relativeSingularHomologyIntFunctor_map_eq_of_homotopy
        R H z

end AlgebraicTopology
