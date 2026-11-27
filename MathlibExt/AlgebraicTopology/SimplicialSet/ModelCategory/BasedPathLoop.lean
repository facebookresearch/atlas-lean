/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
import MathlibExt.AlgebraicTopology.SimplicialSet.IntervalMinimum
import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat
import MathlibExt.AlgebraicTopology.SimplicialSet.ProdStdSimplexCompat
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Based simplicial paths and loops

For a vertex x of a simplicial set X in universe u, the based path object P_xX is the strict
fiber of initial evaluation ev₀:X^{Δ[1]}→X at x. Its distinguished point is the constant path at
x; final evaluation gives p_x:P_xX→X, and the strict fiber at x is the loop object Ω_xX.

For Kan X, p_x is a simplicial fibration and both P_xX and Ω_xX are Kan. These objects and
points form the loop fibration sequence. For every X, precomposition with interval minimum gives
a homotopy from the constant based path to id_{P_xX}; for Kan X all pointed homotopy groups of
P_xX are subsingleton.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
  Simplicial SSet HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

/-- For a simplicial set X in universe u and a vertex x∈X₀, let P_xX be the strict fiber at x of
ev₀:X^{Δ[1]}→X. Its n-simplices are n-parameter simplicial paths whose initial n-simplex is
constant at x; the object is a subcomplex of X^{Δ[1]}. -/
noncomputable def basedPath (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x

/-- For a simplicial set X in universe u and a vertex x∈X₀, let P_xX be the strict fiber at x of
ev₀:X^{Δ[1]}→X. The constant path at x has initial evaluation x, hence defines a vertex of P_xX.
This is the distinguished point used in its endpoint fibration sequence. -/
noncomputable def basedPathPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    basedPath X x _⦋0⦌ :=
  Subcomplex.fiber.basePoint ((constPath X).app _ x) (by
    have h := ConcreteCategory.congr_hom
      (congr_app (eval₀_constPath X) (op ⦋0⦌)) x
    change (eval₀.app (op ⦋0⦌)) ((constPath X).app (op ⦋0⦌) x) = x
    exact h)

/-- For a simplicial set X in universe u and a vertex x∈X₀, let P_xX be the strict fiber at x of
ev₀:X^{Δ[1]}→X. Define p_x:P_xX→X as the inclusion P_xX→X^{Δ[1]} followed by final evaluation
ev₁. Thus a based path is sent to its final vertex. -/
noncomputable def basedPathProj (X : SSet.{u}) (x : X _⦋0⦌) :
    basedPath X x ⟶ X :=
  (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ≫ eval₁

/-- For a simplicial set X in universe u and a vertex x∈X₀, let P_xX be the strict fiber at x of
ev₀:X^{Δ[1]}→X. The loop object Ω_xX is the strict fiber at x of final evaluation p_x:P_xX→X.
Its simplicial paths have both endpoint simplices constant at x. -/
noncomputable def loopSpace (X : SSet.{u}) (x : X _⦋0⦌) : SSet.{u} :=
  Subcomplex.fiber (basedPathProj X x) x

/-- For a simplicial set X in universe u and a vertex x∈X₀, let P_xX be the strict fiber at x of
ev₀:X^{Δ[1]}→X. Final evaluation p_x sends the distinguished constant based-path vertex to x:
(p_x)_0(const_x)=x. -/
@[simp]
lemma basedPathProj_basedPathPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    (basedPathProj X x).app _ (basedPathPoint X x) = x := by
  have h := ConcreteCategory.congr_hom
    (congr_app (eval₁_constPath X) (op ⦋0⦌)) x
  change (eval₁.app (op ⦋0⦌)) ((constPath X).app (op ⦋0⦌) x) = x
  exact h

private theorem basedPath_isPullback (X : SSet.{u}) (x : X _⦋0⦌) :
    IsPullback (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι
      (basedPathProj X x) evalPair (lift (SSet.const x) (𝟙 X)) := by
  dsimp [basedPathProj, basedPath]
  refine { w := ?_, isLimit' := ?_ }
  · apply CartesianMonoidalCategory.hom_ext
    · simp [Category.assoc]
    · simp [Category.assoc]
  · have hRange :
        ∀ (s : PullbackCone evalPair (lift (SSet.const x) (𝟙 X))),
          Subcomplex.range s.fst ≤
            Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x := by
      intro s
      rw [Subcomplex.range_le_fiber_iff]
      calc
        s.fst ≫ eval₀ = s.fst ≫ evalPair ≫ fst X X := by
          simp
        _ = s.snd ≫ lift (SSet.const x) (𝟙 X) ≫ fst X X := by
          simpa only [← Category.assoc] using s.condition =≫ fst X X
        _ = SSet.const x := by simp
    refine ⟨PullbackCone.IsLimit.mk (by
        apply CartesianMonoidalCategory.hom_ext
        · simp [Category.assoc]
        · simp [Category.assoc])
      (fun s ↦ Subcomplex.lift s.fst (hRange s))
      (fun s ↦ Subcomplex.lift_ι s.fst (hRange s))
      (fun s ↦ ?_)
      (fun s m h₁ h₂ ↦ ?_)⟩
    · rw [← Category.assoc, Subcomplex.lift_ι]
      have h := s.condition =≫ snd X X
      simpa [Category.assoc] using h
    · apply (cancel_mono
        (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι).mp
      rw [h₁, Subcomplex.lift_ι]

/-- For a Kan simplicial set X in universe u and x∈X₀, final evaluation p_x:P_xX→X is a simplicial
fibration. Here P_xX is the strict fiber of ev₀:X^{Δ[1]}→X at x. -/
instance basedPathProj_fibration (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : Fibration (basedPathProj X x) := by
  rw [modelCategoryQuillen.fibration_iff]
  exact MorphismProperty.of_isPullback (basedPath_isPullback X x) (by
    rw [← modelCategoryQuillen.fibration_iff]
    infer_instance)

/-- For a Kan simplicial set X in universe u and x∈X₀, P_xX—the strict fiber at x of initial
evaluation X^{Δ[1]}→X—is Kan. -/
instance basedPath_kanComplex (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : KanComplex (basedPath X x) := by
  dsimp [basedPath]
  infer_instance

/-- For a Kan simplicial set X in universe u and x∈X₀, the loop object Ω_xX is Kan. It is the strict
fiber at x of final evaluation p_x:P_xX→X. -/
instance loopSpace_kanComplex (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : KanComplex (loopSpace X x) := by
  dsimp [loopSpace]
  infer_instance

/-- For a Kan simplicial set X in universe u and x∈X₀, define the pointed fibration sequence with
total space P_xX, base X, map final evaluation p_x, total point the constant based path and base
point x. Its strict fiber is Ω_xX. -/
noncomputable def loopFibrationSequence (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : FibrationSequence.{u} where
  E := basedPath X x
  B := X
  p := basedPathProj X x
  fibration_p := inferInstance
  fibrant_B := inferInstance
  e := basedPathPoint X x
  b := x
  hb := basedPathProj_basedPathPoint X x

/-!
## Contraction from the constant based path

For a based path α and interval parameter t, precomposing α with s↦min(s,t) gives the constant
path at x when t=0 and α when t=1. This preserves the initial-point condition and produces a
simplicial homotopy from the constant based-path map to id_{P_xX}.
-/

private noncomputable def pathContractionCurried (X : SSet.{u}) :
    pathSpace X ⟶ (ihom (Δ[1] : SSet.{u})).obj (pathSpace X) :=
  (MonoidalClosed.pre intervalMinMap).app X ≫
    MonoidalClosed.ihomCurry (Δ[1] : SSet.{u}) Δ[1] X

private noncomputable def pathContractionMap (X : SSet.{u}) :
    pathSpace X ⊗ Δ[1] ⟶ pathSpace X :=
  (β_ (pathSpace X) (Δ[1] : SSet.{u})).hom ≫
    MonoidalClosed.uncurry (pathContractionCurried X)

private lemma pathContractionMap_eq (X : SSet.{u}) :
    pathContractionMap X =
      (β_ (pathSpace X) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.curry ((α_ (Δ[1] : SSet.{u}) Δ[1] (pathSpace X)).inv ≫
          MonoidalClosed.uncurry ((MonoidalClosed.pre intervalMinMap).app X)) := by
  dsimp [pathContractionMap, pathContractionCurried]
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_ihomCurry, ← MonoidalClosed.curry_natural_left]
  congr 1

private lemma pathContractionMap_timeZero (X : SSet.{u}) :
    ι₀ ≫ pathContractionMap X = eval₀ ≫ constPath X := by
  rw [pathContractionMap_eq, MonoidalClosed.uncurry_pre,
    ← cancel_epi (stdSimplex.rightUnitor _).hom,
    stdSimplex.rightUnitor_hom_ι₀_assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    ← MonoidalClosed.curry_natural_left,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    intervalMinMap_zero_right,
    ← MonoidalClosed.curry_natural_left,
    eval₀_constPath_eq_pre_constZero]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_pre]
  rfl

private lemma pathContractionMap_timeOne (X : SSet.{u}) :
    ι₁ ≫ pathContractionMap X = 𝟙 (pathSpace X) := by
  rw [pathContractionMap_eq, MonoidalClosed.uncurry_pre,
    ← cancel_epi (stdSimplex.rightUnitor _).hom,
    stdSimplex.rightUnitor_hom_ι₁_assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    Category.comp_id,
    ← MonoidalClosed.curry_natural_left,
    associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    intervalMinMap_one_right]
  apply MonoidalClosed.uncurry_injective
  rfl

private lemma pathContractionMap_preZero (X : SSet.{u}) :
    pathContractionMap X ≫
        (MonoidalClosed.pre
          (SSet.const (X := (Δ[1] : SSet.{u}))
            (stdSimplex.obj₀Equiv.{u}.symm 0))).app X =
      CartesianMonoidalCategory.fst (pathSpace X) (Δ[1] : SSet.{u}) ≫
        (MonoidalClosed.pre
          (SSet.const (X := (Δ[1] : SSet.{u}))
            (stdSimplex.obj₀Equiv.{u}.symm 0))).app X := by
  rw [pathContractionMap_eq, Category.assoc,
    MonoidalClosed.curry_pre_app]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_pre_app]
  rw [MonoidalClosed.uncurry_pre]
  have hfst : MonoidalClosed.uncurry (fst (pathSpace X) (Δ[1] : SSet.{u})) =
      (Δ[1] : SSet.{u}) ◁ fst (pathSpace X) (Δ[1] : SSet.{u}) ≫
        (ihom.ev (Δ[1] : SSet.{u})).app X := by
    simpa only [Category.comp_id, MonoidalClosed.uncurry_id_eq_ev] using
      (MonoidalClosed.uncurry_natural_left (A := (Δ[1] : SSet.{u}))
        (fst (pathSpace X) (Δ[1] : SSet.{u})) (𝟙 (pathSpace X)))
  rw [hfst]
  have hpre :
      (Δ[1] : SSet.{u}) ◁ (β_ (pathSpace X) (Δ[1] : SSet.{u})).hom ≫
        SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0) ▷ (Δ[1] ⊗ pathSpace X) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[1] (pathSpace X)).inv ≫
        intervalMinMap ▷ pathSpace X =
      SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0) ▷ (pathSpace X ⊗ Δ[1]) ≫
        (Δ[1] : SSet.{u}) ◁ fst (pathSpace X) (Δ[1] : SSet.{u}) := by
    apply CartesianMonoidalCategory.hom_ext
    · ext ⟨⟨n⟩⟩ z i
      change ((intervalMinMap.app (op ⦋n⦌)
        ((SSet.const (stdSimplex.obj₀Equiv.{u}.symm 0)).app (op ⦋n⦌) z.1, z.2.2) :
          (Δ[1] : SSet.{u}) _⦋n⦌) i).val = 0
      rw [intervalMinMap_apply]
      change (min (0 : Fin 2) (z.2.2 i)).val = 0
      exact congrArg Fin.val (min_eq_left (Fin.zero_le _))
    · ext ⟨⟨n⟩⟩ z
      rfl
  simpa only [Category.assoc] using
    congrArg (fun a => a ≫ (ihom.ev (Δ[1] : SSet.{u})).app X) hpre


private lemma basedPathCylinder_evalZero (X : SSet.{u}) (x : X _⦋0⦌) :
    ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
        (Δ[1] : SSet.{u})) ≫ pathContractionMap X ≫ eval₀ =
      SSet.const x := by
  let _ : IsSplitMono (constPath X) :=
    IsSplitMono.mk'
      { retraction := eval₀
        id := eval₀_constPath X }
  apply (cancel_mono (constPath X)).mp
  calc
    ((((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
        (Δ[1] : SSet.{u})) ≫ pathContractionMap X ≫ eval₀) ≫ constPath X) =
        ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
          (Δ[1] : SSet.{u})) ≫
            (pathContractionMap X ≫ (eval₀ ≫ constPath X)) := by
              simp only [Category.assoc]
    _ = ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
          (Δ[1] : SSet.{u})) ≫
            (pathContractionMap X ≫
              (MonoidalClosed.pre
                (SSet.const (X := (Δ[1] : SSet.{u}))
                  (stdSimplex.obj₀Equiv.{u}.symm 0))).app X) := by
                    rw [eval₀_constPath_eq_pre_constZero]
    _ = ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
          (Δ[1] : SSet.{u})) ≫
            (CartesianMonoidalCategory.fst (pathSpace X) (Δ[1] : SSet.{u}) ≫
              (MonoidalClosed.pre
                (SSet.const (X := (Δ[1] : SSet.{u}))
                  (stdSimplex.obj₀Equiv.{u}.symm 0))).app X) := by
                    rw [pathContractionMap_preZero]
    _ = CartesianMonoidalCategory.fst
          ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x) : SSet.{u})
            (Δ[1] : SSet.{u}) ≫
            (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ≫
              (MonoidalClosed.pre
                (SSet.const (X := (Δ[1] : SSet.{u}))
                  (stdSimplex.obj₀Equiv.{u}.symm 0))).app X := by
                    rw [← Category.assoc,
                      CartesianMonoidalCategory.whiskerRight_fst,
                      Category.assoc]
    _ = CartesianMonoidalCategory.fst
          ((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x) : SSet.{u})
            (Δ[1] : SSet.{u}) ≫
            (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ≫
              eval₀ ≫ constPath X := by
                rw [← eval₀_constPath_eq_pre_constZero]
    _ = SSet.const x ≫ constPath X := by
      simp

private noncomputable def basedPathContractionMap
    (X : SSet.{u}) (x : X _⦋0⦌) :
    basedPath X x ⊗ Δ[1] ⟶ basedPath X x :=
  Subcomplex.lift
    (((Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι ▷
      (Δ[1] : SSet.{u})) ≫ pathContractionMap X)
    (by
      rw [Subcomplex.range_le_fiber_iff]
      exact basedPathCylinder_evalZero X x)

private lemma const_basedPathPoint_ι (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.const (X := basedPath X x) (basedPathPoint X x) ≫
        (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι =
      SSet.const (X := basedPath X x) x ≫ constPath X := by
  dsimp [basedPath, basedPathPoint]
  rw [const_comp, const_comp]
  rfl

private lemma basedPathContractionMap_timeZero
    (X : SSet.{u}) (x : X _⦋0⦌) :
    ι₀ ≫ basedPathContractionMap X x =
      SSet.const (basedPathPoint X x) := by
  dsimp [basedPath, basedPathPoint, basedPathContractionMap]
  apply (cancel_mono
    (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι).mp
  simp only [Category.assoc, Subcomplex.lift_ι]
  rw [← Category.assoc, ι₀_comp, Category.assoc, pathContractionMap_timeZero,
    ← Category.assoc, Subcomplex.fiber_ι_comp]
  exact (const_basedPathPoint_ι X x).symm

private lemma basedPathContractionMap_timeOne
    (X : SSet.{u}) (x : X _⦋0⦌) :
    ι₁ ≫ basedPathContractionMap X x =
      𝟙 (basedPath X x) := by
  dsimp [basedPath, basedPathContractionMap]
  apply (cancel_mono
    (Subcomplex.fiber (eval₀ : pathSpace X ⟶ X) x).ι).mp
  simp only [Category.assoc, Subcomplex.lift_ι]
  rw [← Category.assoc, ι₁_comp, Category.assoc, pathContractionMap_timeOne]
  simp

/-- For a simplicial set X in universe u and a vertex x∈X₀, let P_xX be the strict fiber at x of
ev₀:X^{Δ[1]}→X. There is a simplicial homotopy const_{const_x}≃id_{P_xX}. On interval
coordinates the construction precomposes a path α with s↦min(s,t): parameter t=0 gives the
constant based path and t=1 gives α. -/
noncomputable opaque basedPathContraction (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.Homotopy
      (SSet.const (basedPathPoint X x))
      (𝟙 (basedPath X x)) := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm _)
    (SSet.RelativeMorphism.botEquiv.symm _)
  refine
    { h := basedPathContractionMap X x
      h₀ := basedPathContractionMap_timeZero X x
      h₁ := basedPathContractionMap_timeOne X x
      rel := ?_ }
  ext m ⟨⟨y, hy⟩, t⟩
  cases hy

private theorem basedPath_toPoint_W (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    KanComplex.W
      (stdSimplex.isTerminalObj₀.from (basedPath X x)) := by
  let q : basedPath X x ⟶ (Δ[0] : SSet.{u}) :=
    stdSimplex.isTerminalObj₀.from (basedPath X x)
  let s : (Δ[0] : SSet.{u}) ⟶ basedPath X x :=
    SSet.const (basedPathPoint X x)
  let _ : KanComplex (Δ[0] : SSet.{u}) := by
    rw [KanComplex.iff]
    intro n i f hf
    exact ⟨stdSimplex.isTerminalObj₀.from _,
      fun j hj ↦ stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  apply KanComplex.W.of_homotopy q s
  · have hqs : q ≫ s = SSet.const (basedPathPoint X x) := by
      simp [q, s]
    rw [hqs]
    exact basedPathContraction X x
  · have hsq : s ≫ q = 𝟙 (Δ[0] : SSet.{u}) :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [hsq]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm _)
      (SSet.RelativeMorphism.botEquiv.symm _)
    exact SSet.RelativeMorphism.Homotopy.refl _

private theorem subsingleton_pi_stdSimplexZero
    [KanComplex (Δ[0] : SSet.{u})]
    (z : (Δ[0] : SSet.{u}) _⦋0⦌) (n : ℕ) :
    Subsingleton (KanComplex.π n (Δ[0] : SSet.{u}) z) := by
  constructor
  intro a b
  induction a using KanComplex.π.rec with
  | mk p =>
    induction b using KanComplex.π.rec with
    | mk q =>
      rw [KanComplex.π.mk_eq_mk_iff]
      have hpq : p = q := by
        apply SSet.RelativeMorphism.ext
        exact stdSimplex.isTerminalObj₀.hom_ext _ _
      subst q
      exact ⟨SSet.PtSimplex.RelStruct₀.refl p⟩

/-- For a Kan simplicial set X in universe u, a vertex x and every n∈ℕ, π_n(P_xX,const_x) is
subsingleton. The statement includes n=0 and uses the distinguished constant-path vertex of the
strict initial-evaluation fiber. -/
theorem subsingleton_pi_basedPath (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (n : ℕ) :
    Subsingleton
      (KanComplex.π n (basedPath X x) (basedPathPoint X x)) := by
  let q : basedPath X x ⟶ (Δ[0] : SSet.{u}) :=
    stdSimplex.isTerminalObj₀.from (basedPath X x)
  have hW : KanComplex.W q := by
    simpa [q] using basedPath_toPoint_W X x
  let _ : KanComplex (Δ[0] : SSet.{u}) := hW.kanComplex_target
  have hInjective :=
    (hW.bijective_piMap n (basedPathPoint X x)).1
  constructor
  intro a b
  apply hInjective
  exact (subsingleton_pi_stdSimplexZero
    (q.app (op ⦋0⦌) (basedPathPoint X x)) n).elim _ _

end SSet
