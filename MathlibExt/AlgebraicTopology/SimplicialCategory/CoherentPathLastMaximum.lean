/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentSimplex
import Mathlib.Data.Finset.Max
import Mathlib.CategoryTheory.Products.Basic

/-!
# Actual last-front-vertex maps of original coherent interval paths

A path from an original front vertex to the last vertex has a nonempty
finite set of front labels. Its maximum is an actual functor on the
original path-poset Hom category. Original union composition with a
front interval preserves the maximum of the last factor, including the
literal smallest front ordinal.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.PathLastMaximum
variable {n : ℕ}

/-- The original coherent interval path from the supplied front vertex to the actual last vertex. -/
abbrev LastPath (i : Fin (n + 1)) :=
  SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u} (Fin.last (n + 1)))

/-- The finite set of actual original front labels belonging to the supplied interval path. -/
def frontSet (i : Fin (n + 1)) (p : LastPath.{u} i) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun j => ULift.up.{u} j.castSucc ∈ p.I)

/-- Membership in that finite front set is precisely membership of the same original lifted
front vertex. -/
theorem mem_frontSet (i : Fin (n + 1)) (p : LastPath.{u} i) (j : Fin (n + 1)) :
    j ∈ frontSet i p ↔ ULift.up.{u} j.castSucc ∈ p.I := by
  classical
  simp only [frontSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The supplied original front endpoint belongs to its actual finite front set. -/
theorem source_mem (i : Fin (n + 1)) (p : LastPath.{u} i) : i ∈ frontSet i p :=
  (mem_frontSet i p i).mpr p.left

/-- The actual original front set is nonempty because it retains the supplied front endpoint. -/
theorem frontSet_nonempty (i : Fin (n + 1)) (p : LastPath.{u} i) : (frontSet i p).Nonempty
  := ⟨i, source_mem i p⟩

/-- The actual largest original front label in the supplied coherent interval path. -/
def maximum (i : Fin (n + 1)) (p : LastPath.{u} i) : Fin (n + 1) :=
  (frontSet i p).max' (frontSet_nonempty i p)

/-- The maximum is the same actual original front vertex belonging to the supplied path. -/
theorem maximum_mem (i : Fin (n + 1)) (p : LastPath.{u} i) : maximum i p ∈ frontSet i p :=
  Finset.max'_mem _ _

/-- Every original front vertex in the supplied path is bounded by its actual maximum. -/
theorem le_maximum (i : Fin (n + 1)) (p : LastPath.{u} i) (j : Fin (n + 1)) (hj : j ∈
  frontSet i p) :
    j ≤ maximum i p := Finset.le_max' _ j hj

/-- The supplied original front endpoint is bounded by the actual maximum. -/
theorem source_le_maximum (i : Fin (n + 1)) (p : LastPath.{u} i) : i ≤ maximum i p :=
  le_maximum i p i (source_mem i p)

/-- An actual path-poset morphism preserves each original front label. -/
theorem frontSet_mono (i : Fin (n + 1)) {p q : LastPath.{u} i} (f : p ⟶ q) : frontSet i p
  ⊆ frontSet i q := by
  intro j hj
  exact (mem_frontSet i q j).mpr (f.hom.down.down ((mem_frontSet i p j).mp hj))

/-- The actual front maximum is monotone on the original path-poset Hom category. -/
theorem maximum_mono (i : Fin (n + 1)) {p q : LastPath.{u} i} (f : p ⟶ q) : maximum i p
  ≤ maximum i q :=
  le_maximum i q _ (frontSet_mono i f (maximum_mem i p))

/-- The whole original maximum functor, retaining the actual lifted front ordinal vertices. -/
def maximumFunctor (i : Fin (n + 1)) : LastPath.{u} i ⥤ ULift.{u} (Fin (n + 1)) where
  obj p := ULift.up (maximum i p)
  map f := homOfLE (maximum_mono i f)

/-- The original union composition of a front interval and a last interval. -/
def compose (i j : Fin (n + 1))
    (p : SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u} j.castSucc)) (q :
      LastPath.{u} j)
      : LastPath.{u} i :=
  (SimplicialThickening.compFunctor (SimplicialThickening.mk (ULift.up.{u} i.castSucc))
    (SimplicialThickening.mk (ULift.up.{u} j.castSucc)) (SimplicialThickening.mk
      (ULift.up.{u} (Fin.last (n
      + 1))))).obj (p, q)

/-- Original union composition preserves exactly the last factor's actual largest front vertex. -/
theorem maximum_compose (i j : Fin (n + 1))
    (p : SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u} j.castSucc)) (q :
      LastPath.{u} j) :
    maximum i (compose i j p q) = maximum j q := by
  apply le_antisymm
  · apply Finset.max'_le
    intro k hk
    have hmem := (mem_frontSet i (compose i j p q) k).mp hk
    change ULift.up.{u} k.castSucc ∈ p.I ∨ ULift.up.{u} k.castSucc ∈ q.I at hmem
    rcases hmem with hp | hq
    · have hkj := p.le_right (ULift.up.{u} k.castSucc) hp
      have h : k ≤ j := by
        change k.val ≤ j.val at hkj
        exact hkj
      exact h.trans (source_le_maximum j q)
    · exact le_maximum j q k ((mem_frontSet j q k).mpr hq)
  · apply le_maximum i (compose i j p q) (maximum j q)
    apply (mem_frontSet i (compose i j p q) _).mpr
    change ULift.up.{u} (maximum j q).castSucc ∈ p.I ∨ ULift.up.{u} (maximum j q).castSucc ∈ q.I
    exact Or.inr ((mem_frontSet j q _).mp (maximum_mem j q))

/-- The actual whole maximum functor commutes with original coherent composition of a front
interval and a
  last interval. -/
theorem maximumFunctor_compose (i j : Fin (n + 1)) :
    SimplicialThickening.compFunctor (SimplicialThickening.mk (ULift.up.{u} i.castSucc))
        (SimplicialThickening.mk (ULift.up.{u} j.castSucc)) (SimplicialThickening.mk
          (ULift.up.{u} (Fin.last
          (n + 1)))) ⋙ maximumFunctor i =
      CategoryTheory.Prod.snd (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u}
        j.castSucc)) (LastPath.{u} j) ⋙ maximumFunctor j := by
  refine Functor.ext (fun p => ULift.ext (maximum_compose i j p.1 p.2)) ?_
  intro p q f
  exact Subsingleton.elim _ _

/-- The literal smallest front ordinal retains its only original zero label. -/
theorem maximum_zero (i : Fin 1) (p : LastPath.{u} i) : maximum i p = 0 :=
  @Subsingleton.elim (Fin 1) inferInstance _ _

end CategoryTheory.CoherentRealization.PathLastMaximum
