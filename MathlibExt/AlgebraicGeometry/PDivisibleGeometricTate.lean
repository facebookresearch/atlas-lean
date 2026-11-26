/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Torsion points of a p-divisible group via its finite levels

The map from the `T`-points of the level `Gₙ` to the `pⁿ`-torsion of the
colimit of the groups of `T`-points of the levels is bijective.

Source: Scholze--Weinstein, arXiv:1211.6357v2, Section 3.3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleGeometricTate

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.CartesianMonoidalCategory
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisiblePointFunctors
open MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels
open scoped _root_.CategoryTheory.MonObj

/-- The diagram of `T`-points of the levels, valued in commutative groups. -/
private abbrev pointDiagram (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) : ℕ ⥤ CommGrpCat.{0} :=
  pointTower (p := p) (S := S) G ⋙ (evaluation _ _).obj (op T)

/-- Level transitions are monomorphisms, as closed immersions. -/
private theorem transitionMono (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) {n m : ℕ} (f : n ⟶ m) : Mono (G.levels.map f) := by
  have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  rw [hf]
  have : IsClosedImmersion (G.levels.map (homOfLE (leOfHom f))).left :=
    G.closed (leOfHom f)
  exact Over.mono_of_mono_left _

/-- The point diagram acts by postcomposition with the level transition. -/
private theorem diagramMap_apply (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) {n m : ℕ} (f : n ⟶ m)
    (x : (pointDiagram p S G T).obj n) :
    (pointDiagram p S G T).map f x = x ≫ G.levels.map f := rfl

/-- Level maps are injective on `T`-points. -/
private theorem diagramMap_injective (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) {n m : ℕ} (f : n ⟶ m) :
    Function.Injective ((pointDiagram p S G T).map f) := by
  intro x y h
  rw [diagramMap_apply, diagramMap_apply] at h
  have := transitionMono p S G f
  exact (cancel_mono _).mp h

/-- Reinterpret an additive point-group element multiplicatively. -/
private def toMulPoints (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (v : (points p S G).obj (op T)) :
    (pointwisePoints (p := p) (S := S) G).obj (op T) :=
  Additive.toMul v

/-- Reinterpret an additive finite-level point multiplicatively. -/
private def toMulLevel (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ)
    (x : (finitePoints p S G n).obj (op T)) :
    (levelPoints (p := p) (S := S) G n).obj (op T) :=
  Additive.toMul x

/-- Reinterpret a multiplicative finite-level point additively. -/
private def ofMulLevel (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ)
    (y : (levelPoints (p := p) (S := S) G n).obj (op T)) :
    (finitePoints p S G n).obj (op T) :=
  Additive.ofMul y

/-- The two finite-level reinterpretations are inverse. -/
private theorem toMulLevel_ofMulLevel (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ)
    (y : (levelPoints (p := p) (S := S) G n).obj (op T)) :
    toMulLevel p S G T n (ofMulLevel p S G T n y) = y := rfl

/-- The additive-to-multiplicative reinterpretation is injective. -/
private theorem toMulLevel_injective (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ) :
    Function.Injective (toMulLevel p S G T n) := by
  intro a b h
  exact Additive.ext h

/-- The point-group reinterpretation is injective. -/
private theorem toMulPoints_injective (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) :
    Function.Injective (toMulPoints p S G T) := by
  intro a b h
  exact Additive.ext h

/-- Torsion points map to roots of unity in the point colimit. -/
private theorem toMulPoints_pow_of_torsion (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (v : (points p S G).obj (op T))
    (k : ℕ) (h : k • v = 0) : (toMulPoints p S G T v) ^ k = 1 := by
  have e1 : toMulPoints p S G T (k • v) = (toMulPoints p S G T v) ^ k :=
    toMul_nsmul (α := ↥((pointwisePoints (p := p) (S := S) G).obj (op T))) k v
  have e0 : toMulPoints p S G T 0 = 1 := toMul_zero
  rw [h] at e1
  rw [e0] at e1
  exact e1.symm

/-- The pointwise colimit comparison isomorphism. -/
private def colimitIso (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) :
    (pointwisePoints (p := p) (S := S) G).obj (op T) ≅
      colimit (pointDiagram p S G T) :=
  colimitObjIsoColimitCompEvaluation (pointTower (p := p) (S := S) G) (op T)

/-- The colimit inclusion commutes with the comparison isomorphism. -/
private theorem inclusionIso_mul_apply (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ)
    (z : (pointDiagram p S G T).obj n) :
    (colimitIso p S G T).hom
        ((levelInclusion (p := p) (S := S) G n).app (op T) z) =
      colimit.ι (pointDiagram p S G T) n z := by
  have h := ConcreteCategory.congr_hom
    (colimitObjIsoColimitCompEvaluation_ι_app_hom (pointTower (p := p) (S := S) G) n
      (op T)) z
  rw [comp_apply] at h
  exact h

/-- The additive inclusion is the multiplicative one on underlying points. -/
private theorem toAdd_transfer (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ)
    (x : (finitePoints p S G n).obj (op T)) :
    toMulPoints p S G T (((finiteInclusion p S G n).app (op T)).hom x) =
      (levelInclusion (p := p) (S := S) G n).app (op T)
        (toMulLevel p S G T n x) := rfl

/-- The niveau-to-colimit comparison on underlying additive points. -/
private theorem inclusionIso_apply (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ)
    (x : (finitePoints p S G n).obj (op T)) :
    (colimitIso p S G T).hom
        (toMulPoints p S G T (((finiteInclusion p S G n).app (op T)).hom x)) =
      colimit.ι (pointDiagram p S G T) n (toMulLevel p S G T n x) := by
  have h1 := toAdd_transfer p S G T n x
  have h2 := inclusionIso_mul_apply p S G T n (toMulLevel p S G T n x)
  rw [h1]
  exact h2

/-- The comparison map from additive points to the group colimit is injective. -/
private theorem toColimit_injective (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) :
    Function.Injective (fun v : (points p S G).obj (op T) =>
      (colimitIso p S G T).hom (toMulPoints p S G T v)) := by
  intro a b h
  have h' : (colimitIso p S G T).hom (toMulPoints p S G T a) =
      (colimitIso p S G T).hom (toMulPoints p S G T b) := h
  have h2 : (colimitIso p S G T).inv ((colimitIso p S G T).hom
      (toMulPoints p S G T a)) = toMulPoints p S G T a := by
    have h := ConcreteCategory.congr_hom (Iso.hom_inv_id (colimitIso p S G T))
      (toMulPoints p S G T a)
    rw [comp_apply, id_apply] at h
    exact h
  have h3 : (colimitIso p S G T).inv ((colimitIso p S G T).hom
      (toMulPoints p S G T b)) = toMulPoints p S G T b := by
    have h := ConcreteCategory.congr_hom (Iso.hom_inv_id (colimitIso p S G T))
      (toMulPoints p S G T b)
    rw [comp_apply, id_apply] at h
    exact h
  have h4 := congrArg ((colimitIso p S G T).inv) h'
  rw [h2, h3] at h4
  exact toMulPoints_injective p S G T h4

/-- Cocone naturality applied to a point. -/
private theorem colimitW_apply (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) {j k : ℕ} (g : j ⟶ k)
    (x : (pointDiagram p S G T).obj j) :
    colimit.ι (pointDiagram p S G T) k ((pointDiagram p S G T).map g x) =
      colimit.ι (pointDiagram p S G T) j x := by
  have h := ConcreteCategory.congr_hom (colimit.w (pointDiagram p S G T) g) x
  simpa using h

/-- **Torsion points of a p-divisible group via its finite levels.** For a prime $p$, a
$p$-divisible group $G = (G_n)_n$ over a scheme $S$ (`PDivisibleGroup`), an $S$-scheme $T$ and
$n ∈ ℕ$: the map from the $T$-points of the level $G_n$ to the $p^n$-torsion of the colimit of
the groups of $T$-points of the levels (`finiteToTorsion`) is bijective. -/
public theorem finite_to_torsion_bijective
    (p : ℕ) [Fact p.Prime] (S : Scheme.{0}) (G : PDivisibleGroup S p)
    (T : Over S) (n : ℕ) : Function.Bijective (finiteToTorsion p S G T n) := by
  constructor
  · intro x y h
    have hval : (((finiteInclusion p S G n).app (op T)).hom x) =
        (((finiteInclusion p S G n).app (op T)).hom y) :=
      congrArg Subtype.val h
    have hcon : (colimitIso p S G T).hom
          (toMulPoints p S G T (((finiteInclusion p S G n).app (op T)).hom x)) =
        (colimitIso p S G T).hom
          (toMulPoints p S G T (((finiteInclusion p S G n).app (op T)).hom y)) :=
      congrArg ((colimitIso p S G T).hom)
        (congrArg (toMulPoints p S G T) hval)
    have e1x := inclusionIso_apply p S G T n x
    have e1y := inclusionIso_apply p S G T n y
    have hcol : colimit.ι (pointDiagram p S G T) n (toMulLevel p S G T n x) =
        colimit.ι (pointDiagram p S G T) n (toMulLevel p S G T n y) := by
      rw [← e1x, ← e1y]
      exact hcon
    obtain ⟨k, f, g, hfg⟩ :=
      (Concrete.colimit_rep_eq_iff_exists (pointDiagram p S G T) _ _).mp hcol
    have fgg : f = g := Subsingleton.elim _ _
    rw [fgg] at hfg
    have hxy := diagramMap_injective p S G T g hfg
    exact toMulLevel_injective p S G T n hxy
  · intro t
    have hmem : (p ^ n) • (t.val) = 0 :=
      AddSubgroup.torsionBy.nsmul_iff.mp t.property
    have hpow : (toMulPoints p S G T t.val) ^ (p ^ n) = 1 :=
      toMulPoints_pow_of_torsion p S G T t.val (p ^ n) hmem
    set c : ↥(colimit (pointDiagram p S G T)) :=
      (colimitIso p S G T).hom (toMulPoints p S G T t.val) with hc
    have hc_pow : c ^ (p ^ n) = 1 := by
      have h1 : ((colimitIso p S G T).hom (toMulPoints p S G T t.val)) ^ (p ^ n) =
          (colimitIso p S G T).hom ((toMulPoints p S G T t.val) ^ (p ^ n)) :=
        (map_pow _ _ _).symm
      rw [hc, h1, hpow, map_one]
    obtain ⟨m, z, hmz⟩ := Concrete.colimit_exists_rep (pointDiagram p S G T) c
    have hzp : (colimit.ι (pointDiagram p S G T) m) (z ^ (p ^ n)) =
        (colimit.ι (pointDiagram p S G T) m) 1 := by
      rw [map_pow, hmz, hc_pow, map_one]
    obtain ⟨k, f, g, hfg⟩ :=
      (Concrete.colimit_rep_eq_iff_exists (pointDiagram p S G T) _ _).mp hzp
    have fgg : f = g := Subsingleton.elim _ _
    rw [fgg, map_pow, map_one] at hfg
    set w : (pointDiagram p S G T).obj k :=
      (pointDiagram p S G T).map g z with hw
    have hkL : k ≤ n + max k n :=
      Nat.le_trans (Nat.le_max_left k n) (Nat.le_add_left (max k n) n)
    set wL : (pointDiagram p S G T).obj (n + max k n) :=
      (pointDiagram p S G T).map (homOfLE hkL) w with hwL
    have hwL_pow : wL ^ (p ^ n) = 1 := by
      rw [hwL, ← map_pow, hfg, map_one]
    have h1 : (wL : T ⟶ G.levels.obj (n + max k n)) ^ (p ^ n) = 1 := hwL_pow
    have mp := multiplication_point S (G.levels.obj (n + max k n)) (p ^ n) T
      (wL : T ⟶ G.levels.obj (n + max k n))
    have rfl1 : (1 : T ⟶ G.levels.obj (n + max k n)) =
        toUnit T ≫ η[G.levels.obj (n + max k n)] := rfl
    have hw' : (wL : T ⟶ G.levels.obj (n + max k n)) ≫
          multiply S (G.levels.obj (n + max k n)) (p ^ n) =
        toUnit T ≫ η[G.levels.obj (n + max k n)] :=
      mp.trans (h1.trans rfl1)
    obtain ⟨l, hl, -⟩ := IsPullback.exists_lift (G.kernel n (max k n))
      (wL : T ⟶ G.levels.obj (n + max k n)) (toUnit T) hw'
    refine ⟨ofMulLevel p S G T n l, ?_⟩
    refine Subtype.ext ?_
    change (((finiteInclusion p S G n).app (op T)).hom
      (ofMulLevel p S G T n l)) = t.val
    have hφ : (colimitIso p S G T).hom
          (toMulPoints p S G T (((finiteInclusion p S G n).app (op T)).hom
            (ofMulLevel p S G T n l))) =
        (colimitIso p S G T).hom (toMulPoints p S G T t.val) := by
      have r1 := inclusionIso_apply p S G T n (ofMulLevel p S G T n l)
      have hoM := toMulLevel_ofMulLevel p S G T n l
      have e1 : colimit.ι (pointDiagram p S G T) n l =
          colimit.ι (pointDiagram p S G T) (n + max k n) wL := by
        have h1 := colimitW_apply p S G T (homOfLE (Nat.le_add_right n (max k n))) l
        have d1 := diagramMap_apply p S G T (homOfLE (Nat.le_add_right n (max k n))) l
        have m1 : (pointDiagram p S G T).map
            (homOfLE (Nat.le_add_right n (max k n))) l = wL := d1.trans hl
        have c1 := congrArg (colimit.ι (pointDiagram p S G T) (n + max k n)) m1
        exact h1.symm.trans c1
      have e2 : colimit.ι (pointDiagram p S G T) (n + max k n) wL =
          colimit.ι (pointDiagram p S G T) k w := by
        have h2 := colimitW_apply p S G T (homOfLE hkL) w
        rw [← hwL] at h2
        exact h2
      have e3 : colimit.ι (pointDiagram p S G T) k w =
          colimit.ι (pointDiagram p S G T) m z := by
        have h3 := colimitW_apply p S G T g z
        rw [← hw] at h3
        exact h3
      calc (colimitIso p S G T).hom
              (toMulPoints p S G T (((finiteInclusion p S G n).app (op T)).hom
                (ofMulLevel p S G T n l)))
          = colimit.ι (pointDiagram p S G T) n
              (toMulLevel p S G T n (ofMulLevel p S G T n l)) := r1
        _ = colimit.ι (pointDiagram p S G T) n l := congrArg _ hoM
        _ = colimit.ι (pointDiagram p S G T) (n + max k n) wL := e1
        _ = colimit.ι (pointDiagram p S G T) k w := e2
        _ = colimit.ι (pointDiagram p S G T) m z := e3
        _ = c := hmz
        _ = (colimitIso p S G T).hom (toMulPoints p S G T t.val) := hc.symm
    exact toColimit_injective p S G T hφ

end WantedExt.AlgebraicGeometry.PDivisibleGeometricTate
