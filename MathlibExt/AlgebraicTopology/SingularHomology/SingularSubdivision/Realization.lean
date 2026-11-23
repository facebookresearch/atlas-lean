/-
Copyright (c) 2025 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.SingularSubdivision.Operators

/-!
# Realization of singular subdivision

Compatibility of geometric realization with the singular subdivision operator.
-/

@[expose] public section

open CategoryTheory Simplicial SimplexCategory SimplicialObject Matrix Limits Opposite

namespace AlgebraicTopology

universe u v w

noncomputable def univIterChainULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n k : ℕ) :
    R ⟶ (sChain (SimplexCategory.toTop.{w}.obj
      (SimplexCategory.mk n)) R).X n :=
  univFundULift (C := C) R n ≫
    (genericSingSubdivIterHomULift R
      (SimplexCategory.toTop.{w}.obj (SimplexCategory.mk n)) k).f n

set_option backward.isDefEq.respectTransparency false in
theorem sigma_ι_genericSingSubdivIterULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n k : ℕ) (X : TopCat.{w})
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    Sigma.ι
          (fun _ : (TopCat.toSSet.obj X).obj
            (Opposite.op (SimplexCategory.mk n)) => R) σ ≫
        (genericSingSubdivIterHomULift R X k).f n =
      univIterChainULift (C := C) R n k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom X
              (Opposite.op (SimplexCategory.mk n)) σ))).f n := by
  let stdTop : TopCat.{w} := SimplexCategory.toTop.{w}.obj (SimplexCategory.mk n)
  let f : stdTop ⟶ X :=
    TopCat.toSSetTopHom X (Opposite.op (SimplexCategory.mk n)) σ
  let chainF : sChain stdTop R ⟶ sChain X R :=
    ((singularChainComplexFunctor C).obj R).map f
  have hNatChain :
      chainF ≫ genericSingSubdivIterHomULift R X k =
        genericSingSubdivIterHomULift R stdTop k ≫ chainF := by
    have h := ((genericSingSubdivIterNatTransULift C k).app R).naturality f
    simp only [genericSingSubdivIterNatTransULift_app_app] at h
    exact h
  have hNat :
      chainF.f n ≫ (genericSingSubdivIterHomULift R X k).f n =
        (genericSingSubdivIterHomULift R stdTop k).f n ≫ chainF.f n := by
    calc
      chainF.f n ≫ (genericSingSubdivIterHomULift R X k).f n =
          (chainF ≫ genericSingSubdivIterHomULift R X k).f n := by
        rw [HomologicalComplex.comp_f]
      _ = (genericSingSubdivIterHomULift R stdTop k ≫ chainF).f n := by
        rw [hNatChain]
      _ = (genericSingSubdivIterHomULift R stdTop k).f n ≫ chainF.f n := by
        rw [HomologicalComplex.comp_f]
  calc
    Sigma.ι
          (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) => R) σ ≫
        (genericSingSubdivIterHomULift R X k).f n =
      (univFundULift (C := C) R n ≫ chainF.f n) ≫
        (genericSingSubdivIterHomULift R X k).f n := by
          exact congrArg
            (fun t => t ≫ (genericSingSubdivIterHomULift R X k).f n)
            (univFundULift_comp_singChainMap (R := R) (C := C) X n σ).symm
    _ = univFundULift (C := C) R n ≫
          (chainF.f n ≫ (genericSingSubdivIterHomULift R X k).f n) := by
        rw [Category.assoc]
    _ = univFundULift (C := C) R n ≫
          ((genericSingSubdivIterHomULift R stdTop k).f n ≫ chainF.f n) := by
        rw [hNat]
    _ = (univFundULift (C := C) R n ≫
          (genericSingSubdivIterHomULift R stdTop k).f n) ≫ chainF.f n := by
        rw [Category.assoc]
    _ = univIterChainULift (C := C) R n k ≫ chainF.f n := rfl

private theorem liftedStdAffine_subdivision_affine_bridge
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {n k : ℕ}
    (τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))
    (hτ : ∀ i, τ i ∈ liftedStdSimplex.{w} n) :
    (SSet.ιChainComplex
          (X := linSSet (ULift.{w} (Fin (k + 1) → ℝ)))
          (R := R) (liftedStdAffine.{w} k) ≫
        subdivision R (ULift.{w} (Fin (k + 1) → ℝ)) k) ≫
        ((linearChainComplexFunctor R).map
          (TypeCat.ofHom (liftedSimplexLinMap τ))).f k ≫
        liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f k =
      (SSet.ιChainComplex
          (X := linSSet (ULift.{w} (Fin (k + 1) → ℝ)))
          (R := R) (liftedStdAffine.{w} k) ≫
        subdivision R (ULift.{w} (Fin (k + 1) → ℝ)) k) ≫
        liftIn (R := R) (liftedStdSimplex.{w} k) k ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} k)
          (convex_liftedStdSimplex.{w} k)).f k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedSimplexTopMap τ hτ))).f k := by
  exact affine_bridge_set
    (convex_liftedStdSimplex.{w} k)
    (convex_liftedStdSimplex.{w} n)
    (fun ρ hρ i => subdivSimplices_liftedStdAffine_mem hρ i)
    (liftedSimplexLinMap τ) (liftedSimplexLinMap_mem hτ)
    (subdivision_mem_chainSpan (R := R) k (liftedStdAffine.{w} k))

private theorem chainMap_liftedStdSimplexTopHom_comp_realizeIn
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {n k : ℕ}
    (τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))
    (hτ : ∀ i, τ i ∈ liftedStdSimplex.{w} n) :
    (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} k))).f k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (TopCat.toSSetTopHom (TopCat.of (liftedStdSimplex.{w} n))
              (Opposite.op (SimplexCategory.mk k))
              ((realizeInNatTrans (liftedStdSimplex.{w} n)
                (convex_liftedStdSimplex.{w} n)).app
                  (Opposite.op (SimplexCategory.mk k)) ⟨τ, hτ⟩)))).f k =
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedSimplexTopMap τ hτ))).f k := by
  rw [← HomologicalComplex.comp_f]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [liftedStdSimplexTopHom_comp_toSSetTopHom_realizeIn]

set_option backward.isDefEq.respectTransparency false in
private theorem realize_comp_genericSingSubdivULift_generator
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {n k : ℕ}
    (τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))
    (hτ : ∀ i, τ i ∈ liftedStdSimplex.{w} n) :
    (SSet.ιChainComplex
          (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R) τ ≫
        liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f k) ≫
        genericSingSubdivULift R (TopCat.of (liftedStdSimplex.{w} n)) k =
      SSet.ιChainComplex
          (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R) τ ≫
        subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k ≫
        liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f k := by
  let ιτ := SSet.ιChainComplex
    (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R) τ
  let στ : (linSSetIn (ULift.{w} (Fin (n + 1) → ℝ))
      (liftedStdSimplex.{w} n)).obj
        (Opposite.op (SimplexCategory.mk k)) := ⟨τ, hτ⟩
  change (ιτ ≫ _ ≫ _) ≫ _ = _
  simp only [Category.assoc]
  erw [liftIn_ι_assoc (R := R), dite_eq_left hτ]
  change SSet.ιChainComplex
      (X := linSSetIn (ULift.{w} (Fin (n + 1) → ℝ))
        (liftedStdSimplex.{w} n)) (R := R) στ ≫ _ ≫ _ = _
  erw [realizeInChain_ι_assoc (R := R), genericSingSubdivULift_ι]
  simp only [univSubdivULift, Category.assoc]
  rw [chainMap_liftedStdSimplexTopHom_comp_realizeIn (R := R) τ hτ]
  conv_rhs => rw [← liftedSimplexLinMap_liftedStdAffine τ]
  erw [← linearChainComplexFunctor_map_ι]
  have hnat := subdivision_naturality (C := C) (R := R) (liftedSimplexLinMap τ) k
  simp only [Category.assoc]
  rw [← reassoc_of% hnat]
  simpa only [Category.assoc] using
    (liftedStdAffine_subdivision_affine_bridge (R := R) τ hτ).symm

/-- Realization commutes with generic subdivision on `chainSpan` in an
arbitrary universe. -/
theorem realize_comp_genericSingSubdivULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {n k : ℕ}
    {Y : Set (Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))}
    (hY : ∀ τ ∈ Y, ∀ i, τ i ∈ liftedStdSimplex.{w} n)
    {c : R ⟶ (freemod (C := C) R
      (ULift.{w} (Fin (n + 1) → ℝ))).obj (Opposite.op ⦋k⦌)}
    (hc : c ∈ chainSpan (C := C) R k Y) :
    (c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f k) ≫
        genericSingSubdivULift R (TopCat.of (liftedStdSimplex.{w} n)) k =
      c ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k ≫
        liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f k := by
  induction hc using AddSubgroup.closure_induction with
  | mem c hc =>
    obtain ⟨τ, hτ, rfl⟩ := hc
    exact realize_comp_genericSingSubdivULift_generator R τ (hY τ hτ)
  | zero => simp only [zero_comp]
  | add x y _ _ ihx ihy =>
    simp only [Preadditive.add_comp, ihx, ihy]
  | neg x _ ihx =>
    simp only [Preadditive.neg_comp, ihx]

/-- Realization commutes with iterated generic subdivision on `chainSpan`
    in an arbitrary universe. -/
theorem realized_iterULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {n k : ℕ} (j : ℕ)
    {Y : Set (Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))}
    (hY : ∀ τ ∈ Y, ∀ i, τ i ∈ liftedStdSimplex.{w} n)
    {c : R ⟶ (freemod (C := C) R
      (ULift.{w} (Fin (n + 1) → ℝ))).obj (Opposite.op ⦋k⦌)}
    (hc : c ∈ chainSpan (C := C) R k Y) :
    (c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f k) ≫
        (genericSingSubdivIterHomULift R
          (TopCat.of (liftedStdSimplex.{w} n)) j).f k =
      c ≫ subdivIter R k j ≫
        liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f k := by
  induction j generalizing Y c with
  | zero =>
    rw [genericSingSubdivIterHomULift_zero, subdivIter_zero]
    simp
  | succ j ih =>
    let Y' : Set (Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ)) :=
      {ρ | ∃ τ ∈ Y, ρ ∈ subdivSimplices τ}
    have hY' : ∀ ρ ∈ Y', ∀ i, ρ i ∈ liftedStdSimplex.{w} n := by
      intro ρ hρ i
      obtain ⟨τ, hτ, hρsub⟩ := hρ
      have hτmem : ∀ a, τ a ∈ liftedStdSimplex.{w} n := hY τ hτ
      have hHull : convexHull ℝ (Set.range τ) ⊆
          liftedStdSimplex.{w} n := by
        apply convexHull_min
        · rintro _ ⟨a, rfl⟩
          exact hτmem a
        · exact convex_liftedStdSimplex.{w} n
      exact hHull (hρsub.1 (Set.mem_range_self i))
    have hc' :
        c ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k ∈
          chainSpan (C := C) R k Y' := by
      refine chainSpan_comp_aux (fun τ hτ => ?_) hc
      refine chainSpan_mono (C := C) (R := R) (n := k)
        (X := subdivSimplices τ) (Y := Y') (fun ρ hρ => ?_) ?_
      · change ∃ τ' ∈ Y, ρ ∈ subdivSimplices τ'
        exact ⟨τ, hτ, hρ⟩
      exact subdivision_mem_chainSpan (R := R) k τ
    calc
      (c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
            (realizeInChain (R := R) (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).f k) ≫
          (genericSingSubdivIterHomULift R
            (TopCat.of (liftedStdSimplex.{w} n)) (j + 1)).f k =
        (c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
            (realizeInChain (R := R) (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).f k) ≫
          (genericSingSubdivHomULift R
              (TopCat.of (liftedStdSimplex.{w} n)) ≫
            genericSingSubdivIterHomULift R
              (TopCat.of (liftedStdSimplex.{w} n)) j).f k := by
        rw [genericSingSubdivIterHomULift_succ]
      _ = (c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
            (realizeInChain (R := R) (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).f k) ≫
          ((genericSingSubdivHomULift R
              (TopCat.of (liftedStdSimplex.{w} n))).f k ≫
            (genericSingSubdivIterHomULift R
              (TopCat.of (liftedStdSimplex.{w} n)) j).f k) := by
        rw [HomologicalComplex.comp_f]
      _ = ((c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
            (realizeInChain (R := R) (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).f k) ≫
          (genericSingSubdivHomULift R
            (TopCat.of (liftedStdSimplex.{w} n))).f k) ≫
          (genericSingSubdivIterHomULift R
            (TopCat.of (liftedStdSimplex.{w} n)) j).f k := by
        rw [← Category.assoc]
      _ = ((c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
            (realizeInChain (R := R) (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).f k) ≫
          genericSingSubdivULift R
            (TopCat.of (liftedStdSimplex.{w} n)) k) ≫
          (genericSingSubdivIterHomULift R
            (TopCat.of (liftedStdSimplex.{w} n)) j).f k := by
        rw [genericSingSubdivHomULift_f]
      _ = (c ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k ≫
            liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
            (realizeInChain (R := R) (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).f k) ≫
          (genericSingSubdivIterHomULift R
            (TopCat.of (liftedStdSimplex.{w} n)) j).f k := by
        rw [realize_comp_genericSingSubdivULift (R := R) hY hc]
      _ = c ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k ≫
          subdivIter R k j ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f k := by
        have hIter := ih hY' hc'
        calc
          (c ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k ≫
                liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
                (realizeInChain (R := R) (liftedStdSimplex.{w} n)
                  (convex_liftedStdSimplex.{w} n)).f k) ≫
              (genericSingSubdivIterHomULift R
                (TopCat.of (liftedStdSimplex.{w} n)) j).f k =
            ((c ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k) ≫
                liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
                (realizeInChain (R := R) (liftedStdSimplex.{w} n)
                  (convex_liftedStdSimplex.{w} n)).f k) ≫
              (genericSingSubdivIterHomULift R
                (TopCat.of (liftedStdSimplex.{w} n)) j).f k := by
              simp only [Category.assoc]
          _ = (c ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k) ≫
                subdivIter R k j ≫
                liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
                (realizeInChain (R := R) (liftedStdSimplex.{w} n)
                  (convex_liftedStdSimplex.{w} n)).f k := hIter
          _ = c ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k ≫
                subdivIter R k j ≫
                liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
                (realizeInChain (R := R) (liftedStdSimplex.{w} n)
                  (convex_liftedStdSimplex.{w} n)).f k := by
              simp only [Category.assoc]
      _ = c ≫
          (subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) k ≫
            subdivIter R k j) ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f k := by
        simp only [Category.assoc]
      _ = c ≫ subdivIter R k (j + 1) ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) k ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f k := by
        rw [subdivIter_succ]

set_option backward.isDefEq.respectTransparency false in
/-- The lifted universal iterated chain equals the realized subdivision
chain postcomposed with the `liftedStdSimplexTopHom` chain map. -/
theorem univIterChainULift_eq
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n k : ℕ) :
    univIterChainULift (C := C) R n k =
      SSet.ιChainComplex
          (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
          (liftedStdAffine.{w} n) ≫
        subdivIter R n k ≫
        liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n := by
  let liftedTop : TopCat.{w} := TopCat.of (liftedStdSimplex.{w} n)
  let stdTop : TopCat.{w} := SimplexCategory.toTop.{w}.obj (SimplexCategory.mk n)
  let f : liftedTop ⟶ stdTop := liftedStdSimplexTopHom.{w} n
  let chainMap : sChain liftedTop R ⟶ sChain stdTop R :=
    ((SSet.chainComplexFunctor C).obj R).map (TopCat.toSSet.map f)
  have hNatChain :
      chainMap ≫ genericSingSubdivIterHomULift R stdTop k =
        genericSingSubdivIterHomULift R liftedTop k ≫ chainMap := by
    have h := ((genericSingSubdivIterNatTransULift C k).app R).naturality f
    simp only [genericSingSubdivIterNatTransULift_app_app] at h
    exact h
  have hNat :
      chainMap.f n ≫ (genericSingSubdivIterHomULift R stdTop k).f n =
        (genericSingSubdivIterHomULift R liftedTop k).f n ≫ chainMap.f n := by
    exact congrArg (fun g => g.f n) hNatChain
  have hY : ∀ τ ∈ ({liftedStdAffine.{w} n} :
      Set (Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ))),
      ∀ i, τ i ∈ liftedStdSimplex.{w} n := by
    intro τ hτ i
    rw [Set.mem_singleton_iff] at hτ
    subst hτ
    exact liftedStdAffine_mem_liftedStdSimplex.{w} n i
  have hc : SSet.ιChainComplex
        (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
        (liftedStdAffine.{w} n) ∈
      chainSpan (C := C) R n ({liftedStdAffine.{w} n} :
        Set (Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ))) :=
    sigma_ι_mem_chainSpan (n := n) (X := {liftedStdAffine.{w} n}) rfl
  have hReal := realized_iterULift (R := R) k hY hc
  calc
    univIterChainULift (C := C) R n k =
        ((SSet.ιChainComplex
            (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
            (liftedStdAffine.{w} n) ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f n ≫ chainMap.f n) ≫
          (genericSingSubdivIterHomULift R stdTop k).f n) := rfl
    _ = (SSet.ιChainComplex
            (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
            (liftedStdAffine.{w} n) ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f n) ≫
        (chainMap.f n ≫
          (genericSingSubdivIterHomULift R stdTop k).f n) := by
      simp only [Category.assoc]
    _ = (SSet.ιChainComplex
            (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
            (liftedStdAffine.{w} n) ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f n) ≫
        ((genericSingSubdivIterHomULift R liftedTop k).f n ≫
          chainMap.f n) := by rw [hNat]
    _ = ((SSet.ιChainComplex
            (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
            (liftedStdAffine.{w} n) ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f n) ≫
        (genericSingSubdivIterHomULift R liftedTop k).f n) ≫
          chainMap.f n := by simp only [Category.assoc]
    _ = (SSet.ιChainComplex
            (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
            (liftedStdAffine.{w} n) ≫
          subdivIter R n k ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f n) ≫
        chainMap.f n := congrArg (fun g => g ≫ chainMap.f n) hReal
    _ = SSet.ιChainComplex
            (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
            (liftedStdAffine.{w} n) ≫
          subdivIter R n k ≫
          liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f n ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n := by
      simp only [chainMap, f, Category.assoc]

end AlgebraicTopology
