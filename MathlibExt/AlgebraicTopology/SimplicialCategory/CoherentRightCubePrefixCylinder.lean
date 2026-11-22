/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCylinder

/-!
# Actual original prefix cylinders for right-cube relations

The original zero-to-middle prefix is kept at cylinder zero and becomes
its full original front interval at cylinder one. Together with the
actual suffix cylinder its union is the cylinder of the original whole
union chain. This is an equality of original path chains before any
quotient or weak-resolution conclusion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubePrefixCylinder
open PathLastMaximum RightCubeCylinder RightCubeFullPath
variable {n : ℕ}

/-- The original front-prefix path category to a supplied original middle vertex. -/
abbrev Prefix (i : Fin (n + 1)) :=
  SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} i.castSucc)

/-- The actual full original front interval at the supplied middle vertex. -/
def full (i : Fin (n + 1)) : Prefix.{u} i where
  I := Set.Iic (ULift.up.{u} i.castSucc)
  left := by change ULift.up.{u} (0 : Fin (n + 2)) ≤ ULift.up i.castSucc; exact Fin.zero_le _
  right := by change ULift.up.{u} i.castSucc ≤ ULift.up i.castSucc; exact le_rfl
  left_le k _ := Fin.zero_le k.down
  le_right _ hk := hk

/-- Original front-prefix inclusion in the same supplied full interval. -/
theorem le_full (i : Fin (n + 1)) (p : Prefix.{u} i) : p.I ⊆ (full i).I :=
  fun k hk => p.le_right k hk

/-- The actual front-prefix path selected by an original interval label. -/
def select (i : Fin (n + 1)) (p : Prefix.{u} i) (t : Fin 2) : Prefix.{u} i :=
  if t = 0 then p else full i

/-- Original front-prefix inclusion and increasing interval labels preserve the actual prefix selector. -/
theorem select_mono (i : Fin (n + 1)) {p q : Prefix.{u} i} (f : p ⟶ q) {t s : Fin 2} (h : t ≤ s) :
    (select i p t).I ⊆ (select i q s).I := by
  by_cases hs : s = 0
  · have ht : t = 0 := le_antisymm (hs ▸ h) (Fin.zero_le _)
    simp only [select, ht, hs, ite_true]
    exact f.hom.down.down
  · by_cases ht : t = 0
    · simp only [select, ht, ite_true, ite_eq_right hs]
      exact le_full i p
    · simp only [select, ite_eq_right ht, ite_eq_right hs]
      exact le_rfl

/-- The genuine ordinary cylinder functor of the original front-prefix category. -/
def functor (i : Fin (n + 1)) : Prefix.{u} i × ULift.{u} (Fin 2) ⥤ Prefix.{u} i where
  obj x := select i x.1 x.2.down
  map f := ⟨homOfLE (select_mono i f.1 f.2.down.down)⟩

/-- The whole original front-prefix cylinder chain at the supplied original scalar interval simplex. -/
def chain (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (Prefix.{u} i)).obj q) (t : (Δ[1] : SSet.{u}).obj q) : (nerve (Prefix.{u} i)).obj q :=
  p.prod' ((SSet.stdSimplex.isoNerve.{u} 1).hom.app q t) ⋙ functor i

/-- The union of the two actual full original intervals is the full source-to-last interval. -/
theorem union_full (i : Fin (n + 1)) : compose (0 : Fin (n + 1)) i (full.{u} i) (fullPath.{u} i) = fullPath 0 := by
  apply SimplicialThickening.Path.ext
  ext k
  change (k ≤ ULift.up.{u} i.castSucc ∨ ULift.up.{u} i.castSucc ≤ k) ↔ ULift.up.{u} (0 : Fin (n + 2)) ≤ k
  constructor
  · intro _
    exact Fin.zero_le k.down
  · intro _
    exact le_total _ _

/-- The entire original selected prefix/suffix union is exactly the selected whole original union path. -/
theorem union_select (i : Fin (n + 1)) (p : Prefix.{u} i) (r : LastPath.{u} i) (t : Fin 2) :
    compose 0 i (select i p t) (RightCubeCylinder.select i r t) = RightCubeCylinder.select 0 (compose 0 i p r) t := by
  by_cases ht : t = 0
  · simp only [select, ht, ite_true, RightCubeCylinder.select_zero]
  · simp only [select, RightCubeCylinder.select, ite_eq_right ht]
    exact union_full i

/-- The actual original typed front-prefix and suffix composition functor. -/
def composeFunctor (i : Fin (n + 1)) : Prefix.{u} i × LastPath.{u} i ⥤ LastPath.{u} (0 : Fin (n + 1)) :=
  SimplicialThickening.compFunctor (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (n + 2))))
    (SimplicialThickening.mk (ULift.up.{u} i.castSucc)) (SimplicialThickening.mk (ULift.up.{u} (Fin.last (n + 1))))

/-- The whole original contracted union chain factors as the actual contracted prefix and suffix chains. -/
theorem chain_union (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (Prefix.{u} i)).obj q) (r : (nerve (LastPath.{u} i)).obj q) (t : (Δ[1] : SSet.{u}).obj q) :
    (chain i p t).prod' (RightCubeCylinder.chain i r t) ⋙ composeFunctor i =
      RightCubeCylinder.chain 0 (p.prod' r ⋙ composeFunctor i) t := by
  refine Functor.ext (fun j => union_select i (p.obj j) (r.obj j) (t.down.toOrderHom j)) ?_
  intro j k f
  apply InducedCategory.Hom.ext
  exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.RightCubePrefixCylinder
