/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceSplitting

/-!
# The horizontal graded-piece cokernel

The degreewise splitting of consecutive horizontal filtration stages is
transported through the chain-to-cochain extension.  This identifies the
categorical cokernel of a consecutive-stage map with the direct shifted-column
presentation used to compute the first filtration page.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The natural consecutive-stage cochain sequence whose last term is the
new horizontal column. -/
noncomputable def horizontalNaturalSuccCochainShortComplex (p : ℕ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    ((ComplexShape.embeddingDownNat.extendFunctor C).map
      (horizontalFilteredTotalComplexMap K (Nat.le_succ p)))
    (horizontalNaturalDirectColumnProjectionMap K (p + 1))
    (horizontalNaturalDirectColumnProjectionMap_stageMap_zero K p)

/-- In every supported degree, the natural consecutive-stage cochain
sequence is the previously constructed split degreewise sequence. -/
noncomputable def horizontalNaturalSuccCochainEvalIso (p q : ℕ) :
    horizontalFilteredSuccShortComplex K p q ≅
      (horizontalNaturalSuccCochainShortComplex K p).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ)
          (-((p + 1 : ℕ) : ℤ) - q)) := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingDownNat
  let N : ℕ := p + 1 + q
  let n : ℤ := -((p + 1 : ℕ) : ℤ) - q
  have hn : e.f N = n := by
    dsimp only [e, N, n]
    rw [ComplexShape.embeddingDownNat_f]
    push_cast
    omega
  let S : ShortComplex C := horizontalFilteredSuccShortComplex K p q
  let T : ShortComplex C := (horizontalNaturalSuccCochainShortComplex K p).map
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
  let e₀ : S.X₁ ≅ T.X₁ := ((horizontalFilteredTotalComplex K p).extendXIso e hn).symm
  let e₁ : S.X₂ ≅ T.X₂ :=
    ((horizontalFilteredTotalComplex K (p + 1)).extendXIso e hn).symm
  let e₂ : S.X₃ ≅ T.X₃ := (horizontalDirectColumnCochainXIso K (p + 1) q).symm
  refine ShortComplex.isoMk e₀ e₁ e₂ ?_ ?_
  · change e₀.hom ≫
        (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMap K (Nat.le_succ p)) e).f n = S.f ≫ e₁.hom
    rw [HomologicalComplex.extendMap_f _ _ hn]
    dsimp only [e₀, e₁, S, horizontalFilteredSuccShortComplex]
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  · change e₁.hom ≫ horizontalNaturalDirectColumnProjection K (p + 1) n = S.g ≫ e₂.hom
    dsimp only [n]
    rw [horizontalNaturalDirectColumnProjection_eq_component K (p + 1) q]
    dsimp only [e₁, e₂, S, horizontalFilteredSuccShortComplex,
      horizontalNaturalDirectColumnProjectionComponent]
    simp

omit [HasZeroObject C] in
/-- Before the new horizontal column appears, consecutive filtration stages
are already equal to the full total object. -/
theorem horizontalFilteredTotalMap_isIso_of_le
    {k l n : ℕ} (h : k ≤ l) (hn : n ≤ k) :
    IsIso (horizontalFilteredTotalMap K h n) := by
  have hk : IsIso (horizontalFilteredTotalToTotal K k n) :=
    (horizontalFilteredTotalIsoOfLE K k n hn).isIso_hom
  have hl : IsIso (horizontalFilteredTotalToTotal K l n) :=
    (horizontalFilteredTotalIsoOfLE K l n (hn.trans h)).isIso_hom
  have hcomp : IsIso
      (horizontalFilteredTotalMap K h n ≫
        horizontalFilteredTotalToTotal K l n) := by
    rw [horizontalFilteredTotalMap_toTotal]
    exact hk
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (horizontalFilteredTotalMap K h n)
    (horizontalFilteredTotalToTotal K l n) hl hcomp

/-- Above the support of the new column, the consecutive-stage cochain map
is an isomorphism. -/
theorem horizontalNaturalSuccCochainMap_f_isIso_of_lt
    (p : ℕ) (i : ℤ) (hi : -((p + 1 : ℕ) : ℤ) < i) :
    IsIso ((horizontalNaturalSuccCochainShortComplex K p).f.f i) := by
  by_cases hi0 : i ≤ 0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := by
      refine ⟨(-i).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by lia)]
      lia
    have hn : n ≤ p := by omega
    have hmap : IsIso
        (horizontalFilteredTotalMap K (Nat.le_succ p) n) :=
      horizontalFilteredTotalMap_isIso_of_le K (Nat.le_succ p) hn
    change IsIso ((HomologicalComplex.extendMap
      (horizontalFilteredTotalComplexMap K (Nat.le_succ p))
        ComplexShape.embeddingDownNat).f (-(n : ℤ)))
    rw [HomologicalComplex.extendMap_f _ _
      (i := n) (i' := -(n : ℤ)) (by simp)]
    let _ := hmap
    change IsIso
      (((horizontalFilteredTotalComplex K p).extendXIso
          ComplexShape.embeddingDownNat (by simp)).hom ≫
        horizontalFilteredTotalMap K (Nat.le_succ p) n ≫
        ((horizontalFilteredTotalComplex K (p + 1)).extendXIso
          ComplexShape.embeddingDownNat (by simp)).inv)
    infer_instance
  · have hipos : 0 < i := by lia
    have hsource : IsZero
        (((horizontalFilteredTotalComplex K p).extend
          ComplexShape.embeddingDownNat).X i) :=
      (horizontalFilteredTotalComplex K p).isZero_extend_X
        ComplexShape.embeddingDownNat i (fun n hn => by
          simp only [ComplexShape.embeddingDownNat_f] at hn
          lia)
    have htarget : IsZero
        (((horizontalFilteredTotalComplex K (p + 1)).extend
          ComplexShape.embeddingDownNat).X i) :=
      (horizontalFilteredTotalComplex K (p + 1)).isZero_extend_X
        ComplexShape.embeddingDownNat i (fun n hn => by
          simp only [ComplexShape.embeddingDownNat_f] at hn
          lia)
    exact hsource.isIso htarget _

/-- Every degree of the natural consecutive-stage sequence is split. -/
noncomputable def horizontalNaturalSuccCochainEvalSplitting
    (p : ℕ) (i : ℤ) :
    ((horizontalNaturalSuccCochainShortComplex K p).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting := by
  let S : ShortComplex (CochainComplex C ℤ) := horizontalNaturalSuccCochainShortComplex K p
  let splittingAt (j : ℤ) : Type v :=
    (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) j)).Splitting
  by_cases hi : i ≤ -((p + 1 : ℕ) : ℤ)
  · let q : ℕ := horizontalColumnDegree (p + 1) i
    have hiEq : i = -((p + 1 : ℕ) : ℤ) - q :=
      horizontalColumnDegree_spec (p + 1) i hi
    let known : splittingAt (-((p + 1 : ℕ) : ℤ) - q) :=
      (horizontalFilteredSuccSplitting K p q).ofIso (horizontalNaturalSuccCochainEvalIso K p q)
    exact Eq.mpr (congrArg splittingAt hiEq) known
  · exact ShortComplex.Splitting.ofIsIsoOfIsZero _
      (horizontalNaturalSuccCochainMap_f_isIso_of_lt K p i (by lia))
      (horizontalDirectColumnCochain_isZero_X_of_lt K (p + 1) i (by lia))

/-- The complete-filtration short complex whose cokernel is the direct
horizontal column. -/
noncomputable def horizontalFirstPageDirectColumnShortComplex (p : ℕ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (horizontalFirstPageFiltrationMap K p)
    (horizontalCompleteDirectColumnProjectionMap K p)
    (horizontalFirstPageFiltrationMap_projection_zero K p)

/-- For a positive column, the complete-filtration short complex is the
natural consecutive-stage short complex. -/
noncomputable def horizontalFirstPageSuccShortComplexIso (p : ℕ) :
    horizontalFirstPageDirectColumnShortComplex K (p + 1) ≅
      horizontalNaturalSuccCochainShortComplex K p :=
  ShortComplex.isoMk
    (horizontalCompleteFiltrationCochainMonoLowerSuccIso K p ≪≫
      horizontalNaturalStageCochainIso K p)
    (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p ≪≫
      horizontalNaturalStageCochainIso K (p + 1))
    (Iso.refl _)
    (by
      dsimp [horizontalFirstPageDirectColumnShortComplex,
        horizontalNaturalSuccCochainShortComplex]
      calc
        ((horizontalCompleteFiltrationCochainMonoLowerSuccIso K p).hom ≫
              (horizontalNaturalStageCochainIso K p).hom) ≫
            (ComplexShape.embeddingDownNat.extendFunctor C).map
              (horizontalFilteredTotalComplexMap K (Nat.le_succ p)) =
          (horizontalCompleteFiltrationCochainMonoLowerSuccIso K p).hom ≫
            ((horizontalNaturalStageCochainIso K p).hom ≫
              (ComplexShape.embeddingDownNat.extendFunctor C).map
                (horizontalFilteredTotalComplexMap K (Nat.le_succ p))) :=
          Category.assoc _ _ _
        _ = (horizontalCompleteFiltrationCochainMonoLowerSuccIso K p).hom ≫
            ((ComplexShape.embeddingDownNat.extendFunctor C).map
                ((horizontalTotalFiltration K).toMonoOver.map
                  (homOfLE (Nat.le_succ p))).hom.left ≫
              (horizontalNaturalStageCochainIso K (p + 1)).hom) := by
          rw [horizontalNaturalStageCochainIso_naturality K (Nat.le_succ p)]
        _ = ((horizontalCompleteFiltrationCochainMonoLowerSuccIso K p).hom ≫
              (ComplexShape.embeddingDownNat.extendFunctor C).map
                ((horizontalTotalFiltration K).toMonoOver.map
                  (homOfLE (Nat.le_succ p))).hom.left) ≫
            (horizontalNaturalStageCochainIso K (p + 1)).hom :=
          (Category.assoc _ _ _).symm
        _ = (horizontalFirstPageFiltrationMap K (p + 1) ≫
              (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).hom) ≫
            (horizontalNaturalStageCochainIso K (p + 1)).hom := by
          rw [horizontalFirstPageFiltrationMap_succ_monoIso K p]
        _ = horizontalFirstPageFiltrationMap K (p + 1) ≫
            ((horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).hom ≫
              (horizontalNaturalStageCochainIso K (p + 1)).hom) :=
          Category.assoc _ _ _)
    (by
      dsimp [horizontalFirstPageDirectColumnShortComplex,
        horizontalNaturalSuccCochainShortComplex,
        horizontalCompleteDirectColumnProjectionMap,
        horizontalCompleteSuccDirectColumnProjectionMap,
      horizontalMonoStageDirectColumnProjectionMap]
      simp)

/-- Inclusion of the top-column summand into its horizontal filtration
stage. -/
noncomputable def horizontalFilteredTopInclusion (p q : ℕ) :
    (K.X p).X q ⟶ horizontalFilteredTotalObj K p (p + q) :=
  horizontalFilteredTotalι K p (p + q)
    (horizontalFilteredTopIndex p q)

/-- Filtration stage zero has only its top-column summand. -/
noncomputable def horizontalFilteredTopProjectionZeroIso (q : ℕ) :
    horizontalFilteredTotalObj K 0 (0 + q) ≅ (K.X 0).X q where
  hom := horizontalFilteredTopProjection K 0 q
  inv := horizontalFilteredTopInclusion K 0 q
  hom_inv_id := by
    unfold horizontalFilteredTopProjection horizontalFilteredTopInclusion
      horizontalFilteredTotalι
    apply Sigma.hom_ext
    intro idx
    have hidx : idx = horizontalFilteredTopIndex 0 q := by
      obtain ⟨⟨⟨a, b⟩, hab⟩, ha⟩ := idx
      change a + b = 0 + q at hab
      change a ≤ 0 at ha
      have ha0 : a = 0 := by omega
      subst a
      have hbq : b = q := by omega
      subst b
      apply Subtype.ext
      apply Subtype.ext
      rfl
    subst idx
    rw [← Category.assoc, Sigma.ι_π, dite_eq_left rfl]
    dsimp [horizontalFilteredTopIndex]
    change _ = _ ≫ 𝟙 (∐ fun pq :
      DownNatHorizontalFilteredFiber (0 + q) 0 =>
        (K.X pq.val.val.1).X pq.val.val.2)
    rw [Category.comp_id, Category.id_comp]
  inv_hom_id := by
    simpa [horizontalFilteredTopInclusion, horizontalFilteredTopIndex] using
      horizontalFilteredTopι_topProjection K 0 q

/-- The zeroth-stage projection is an isomorphism in every supported
cochain degree. -/
theorem horizontalCompleteDirectColumnProjectionMap_zero_f_isIso_of_degree
    (q : ℕ) :
    IsIso ((horizontalCompleteDirectColumnProjectionMap K 0).f
      (-(0 : ℤ) - q)) := by
  change IsIso (horizontalDirectColumnProjection K 0 (-(0 : ℤ) - q))
  unfold horizontalDirectColumnProjection
  rw [dite_eq_left
    (show -(0 : ℤ) - (q : ℤ) ≤ -((0 : ℕ) : ℤ) by omega)]
  let q' := horizontalColumnDegree 0 (-(0 : ℤ) - (q : ℤ))
  have htop : IsIso (horizontalFilteredTopProjection K 0 q') :=
    (horizontalFilteredTopProjectionZeroIso K q').isIso_hom
  dsimp [horizontalDirectColumnProjectionComponent]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]
  exact htop

/-- The zeroth complete filtration stage projects isomorphically onto the
zeroth direct column. -/
theorem horizontalCompleteDirectColumnProjectionMap_zero_f_isIso (i : ℤ) :
    IsIso ((horizontalCompleteDirectColumnProjectionMap K 0).f i) := by
  by_cases hi : i ≤ 0
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(0 : ℤ) - q :=
      ⟨horizontalColumnDegree 0 i,
        horizontalColumnDegree_spec 0 i hi⟩
    exact horizontalCompleteDirectColumnProjectionMap_zero_f_isIso_of_degree K q
  · have hipos : 0 < i := by lia
    have hext : IsZero
        (((horizontalFilteredTotalComplex K 0).extend
          ComplexShape.embeddingDownNat).X i) :=
      (horizontalFilteredTotalComplex K 0).isZero_extend_X
        ComplexShape.embeddingDownNat i (fun n hn => by
          simp only [ComplexShape.embeddingDownNat_f] at hn
          lia)
    have hsource : IsZero
        (((horizontalCompleteFiltrationCochainDiagram K).obj
          (horizontalFirstPageUpperIndex 0)).X i) :=
      IsZero.of_iso hext
        ((HomologicalComplex.eval C (ComplexShape.up ℤ) i).mapIso
          (horizontalCompleteFiltrationCochainUpperIso K 0))
    have htarget : IsZero ((horizontalDirectColumnCochain K 0).X i) :=
      horizontalDirectColumnCochain_isZero_X_of_lt K 0 i (by simpa)
    exact hsource.isIso htarget _

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The natural consecutive-stage cochain sequence is short exact. -/
theorem horizontalNaturalSuccCochainShortExact (p : ℕ) :
    (horizontalNaturalSuccCochainShortComplex K p).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact (horizontalNaturalSuccCochainEvalSplitting K p i).shortExact

/-- The complete-filtration sequence is short exact in every positive
horizontal column. -/
theorem horizontalFirstPageSuccShortExact (p : ℕ) :
    (horizontalFirstPageDirectColumnShortComplex K (p + 1)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (horizontalFirstPageSuccShortComplexIso K p).symm
    (horizontalNaturalSuccCochainShortExact K p)

/-- The complete-filtration sequence is short exact in column zero. -/
theorem horizontalFirstPageZeroShortExact :
    (horizontalFirstPageDirectColumnShortComplex K 0).ShortExact := by
  have hsource : IsZero
      ((horizontalFirstPageDirectColumnShortComplex K 0).X₁) := by
    change IsZero ((horizontalCompleteFiltrationCochainDiagram K).obj
      (horizontalFirstPageLowerIndex 0))
    exact horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg K
      (-1 : ℤ) (by omega)
  have hprojection : IsIso
      (horizontalFirstPageDirectColumnShortComplex K 0).g := by
    change IsIso (horizontalCompleteDirectColumnProjectionMap K 0)
    let _ (i : ℤ) : IsIso
        ((horizontalCompleteDirectColumnProjectionMap K 0).f i) :=
      horizontalCompleteDirectColumnProjectionMap_zero_f_isIso K i
    exact HomologicalComplex.Hom.isIso_of_components _
  exact (ShortComplex.Splitting.ofIsZeroOfIsIso _ hsource hprojection).shortExact

/-- Every horizontal filtration quotient is the corresponding direct
shifted column. -/
theorem horizontalFirstPageDirectColumnShortExact (p : ℕ) :
    (horizontalFirstPageDirectColumnShortComplex K p).ShortExact := by
  cases p with
  | zero => exact horizontalFirstPageZeroShortExact K
  | succ p => exact horizontalFirstPageSuccShortExact K p

/-- The direct-column projection exhibits the direct shifted column as the
cokernel of consecutive complete filtration stages. -/
noncomputable def horizontalCompleteDirectColumnProjectionMapIsCokernel
    (p : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (horizontalCompleteDirectColumnProjectionMap K p)
      (horizontalFirstPageFiltrationMap_projection_zero K p)) :=
  (horizontalFirstPageDirectColumnShortExact K p).gIsCokernel

/-- The abstract categorical cokernel of consecutive filtration stages is
canonically isomorphic to the direct shifted column. -/
noncomputable def horizontalFirstPageCokernelUniqueIso (p : ℕ) :
    cokernel (horizontalFirstPageFiltrationMap K p) ≅
      horizontalDirectColumnCochain K p :=
  let f := horizontalFirstPageFiltrationMap K p
  let g := horizontalCompleteDirectColumnProjectionMap K p
  let standard : CokernelCofork f := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)
  let canonical : CokernelCofork f :=
    CokernelCofork.ofπ g (horizontalFirstPageFiltrationMap_projection_zero K p)
  let hStandard : IsColimit standard := cokernelIsCokernel f
  let hCanonical : IsColimit canonical := horizontalCompleteDirectColumnProjectionMapIsCokernel K p
  IsColimit.coconePointUniqueUpToIso hStandard hCanonical

theorem horizontalFirstPageCokernelUniqueIso_hom (p : ℕ) :
    (horizontalFirstPageCokernelUniqueIso K p).hom =
      horizontalFirstPageCokernelToDirectColumn K p := by
  apply (cancel_epi (cokernel.π (horizontalFirstPageFiltrationMap K p))).1
  let f := horizontalFirstPageFiltrationMap K p
  let g := horizontalCompleteDirectColumnProjectionMap K p
  let standard : CokernelCofork f := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)
  let canonical : CokernelCofork f :=
    CokernelCofork.ofπ g (horizontalFirstPageFiltrationMap_projection_zero K p)
  let hStandard : IsColimit standard := cokernelIsCokernel f
  let hCanonical : IsColimit canonical := horizontalCompleteDirectColumnProjectionMapIsCokernel K p
  have hleg := IsColimit.comp_coconePointUniqueUpToIso_hom
    hStandard hCanonical WalkingParallelPair.one
  change cokernel.π (horizontalFirstPageFiltrationMap K p) ≫
      (horizontalFirstPageCokernelUniqueIso K p).hom =
    horizontalCompleteDirectColumnProjectionMap K p at hleg
  exact hleg.trans (cokernel.π_desc _ _ _).symm

/-- Canonical graded-piece isomorphism, normalized so that its forward map
is the previously defined cokernel factor. -/
noncomputable def horizontalFirstPageCokernelIso (p : ℕ) :
    cokernel (horizontalFirstPageFiltrationMap K p) ≅
      horizontalDirectColumnCochain K p where
  hom := horizontalFirstPageCokernelToDirectColumn K p
  inv := (horizontalFirstPageCokernelUniqueIso K p).inv
  hom_inv_id := by
    rw [← horizontalFirstPageCokernelUniqueIso_hom]
    exact (horizontalFirstPageCokernelUniqueIso K p).hom_inv_id
  inv_hom_id := by
    rw [← horizontalFirstPageCokernelUniqueIso_hom]
    exact (horizontalFirstPageCokernelUniqueIso K p).inv_hom_id

noncomputable instance horizontalFirstPageCokernelToDirectColumn_isIso
    (p : ℕ) : IsIso (horizontalFirstPageCokernelToDirectColumn K p) :=
  (horizontalFirstPageCokernelIso K p).isIso_hom

end HomologicalComplex₂

end
