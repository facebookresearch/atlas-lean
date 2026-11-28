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
# Cokernels of consecutive horizontal filtration stages

Let `K` be a first-quadrant bicomplex in a preadditive category with a zero object and finite
coproducts. Consecutive natural filtration stages have degreewise split sequences with new
column `p+1` as quotient. Their chain-to-cochain extensions are split in every integer degree;
above support `-(p+1)`, the inclusion map is an isomorphism.

In an abelian category, the corresponding complete-filtration sequences are short exact,
including column zero with zero lower stage. The direct-column projection is a cokernel of the
consecutive-stage map. The canonical cokernel isomorphism has forward map the specified factor
from the categorical cokernel to the direct shifted column.
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

/-- The natural consecutive-stage cochain short complex.

Extend `F_p → F_(p+1)` to cochain degrees and follow it by projection onto direct column
`p+1`. -/
noncomputable def horizontalNaturalSuccCochainShortComplex (p : ℕ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    ((ComplexShape.embeddingDownNat.extendFunctor C).map
      (horizontalFilteredTotalComplexMap K (Nat.le_succ p)))
    (horizontalNaturalDirectColumnProjectionMap K (p + 1))
    (horizontalNaturalDirectColumnProjectionMap_stageMap_zero K p)

/-- The finite splitting coordinates of a supported cochain degree.

Evaluation of the natural cochain sequence at degree `-(p+1)-q` is isomorphic to the finite
total-degree sequence at `p+1+q`. -/
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
  · have hmap : T.f = e₀.inv ≫ S.f ≫ e₁.hom := by
      change (HomologicalComplex.extendMap
        (horizontalFilteredTotalComplexMap K (Nat.le_succ p)) e).f n = _
      rw [HomologicalComplex.extendMap_f _ _ hn]
      rfl
    exact (congrArg (fun f : T.X₁ ⟶ T.X₂ => e₀.hom ≫ f) hmap).trans
      (e₀.hom_inv_id_assoc (S.f ≫ e₁.hom))
  · have hprojection : T.g = e₁.inv ≫ S.g ≫ e₂.hom := by
      change horizontalNaturalDirectColumnProjection K (p + 1) n = _
      dsimp only [n]
      rw [horizontalNaturalDirectColumnProjection_eq_component K (p + 1) q]
      rfl
    exact (congrArg (fun g : T.X₂ ⟶ T.X₃ => e₁.hom ≫ g) hprojection).trans
      (e₁.hom_inv_id_assoc (S.g ≫ e₂.hom))

omit [HasZeroObject C] in
/-- The finite-stage inclusion after all degree summands are present.

For `k ≤ l` and total degree `n ≤ k`, the map from filtration stage `k` to stage `l` is an
isomorphism in degree `n`. -/
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

/-- The consecutive-stage map above new-column support.

In cochain degree `i>-(p+1)`, the map between extended natural stages `p` and `p+1` is an
isomorphism. -/
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
    let e₀ : ((horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat).X (-(n : ℤ)) ≅
          (horizontalFilteredTotalComplex K p).X n :=
      (horizontalFilteredTotalComplex K p).extendXIso
        ComplexShape.embeddingDownNat (by simp)
    let e₁ : ((horizontalFilteredTotalComplex K (p + 1)).extend
        ComplexShape.embeddingDownNat).X (-(n : ℤ)) ≅
          (horizontalFilteredTotalComplex K (p + 1)).X n :=
      (horizontalFilteredTotalComplex K (p + 1)).extendXIso
        ComplexShape.embeddingDownNat (by simp)
    change IsIso
      (e₀.hom ≫ horizontalFilteredTotalMap K (Nat.le_succ p) n ≫ e₁.inv)
    exact IsIso.comp_isIso'
      (f := e₀.hom)
      (h := horizontalFilteredTotalMap K (Nat.le_succ p) n ≫ e₁.inv)
      e₀.isIso_hom
      (IsIso.comp_isIso'
        (f := horizontalFilteredTotalMap K (Nat.le_succ p) n) (h := e₁.inv)
        hmap e₁.isIso_inv)
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

/-- The splitting of each natural-stage cochain degree sequence.

For every integer cochain degree, the consecutive-stage short complex is split; supported
degrees use the finite summand splitting and unsupported degrees use the inclusion
isomorphism. -/
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

/-- The complete-filtration short complex with direct-column quotient.

The consecutive first-page filtration map followed by the complete direct-column projection
defines the column short complex. -/
noncomputable def horizontalFirstPageDirectColumnShortComplex (p : ℕ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (horizontalFirstPageFiltrationMap K p)
    (horizontalCompleteDirectColumnProjectionMap K p)
    (horizontalFirstPageFiltrationMap_projection_zero K p)

/-- The natural-stage comparison of a positive complete column sequence.

For column `p+1`, the complete-filtration short complex is isomorphic to the natural
consecutive-stage cochain sequence. -/
noncomputable def horizontalFirstPageSuccShortComplexIso (p : ℕ) :
    horizontalFirstPageDirectColumnShortComplex K (p + 1) ≅
      horizontalNaturalSuccCochainShortComplex K p := by
  let S : ShortComplex (CochainComplex C ℤ) :=
    horizontalFirstPageDirectColumnShortComplex K (p + 1)
  let T : ShortComplex (CochainComplex C ℤ) := horizontalNaturalSuccCochainShortComplex K p
  let F : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  let A : CochainComplex C ℤ :=
    F.obj (((horizontalTotalFiltration K).toMonoOver.obj p).obj.left)
  let B : CochainComplex C ℤ :=
    F.obj (((horizontalTotalFiltration K).toMonoOver.obj (p + 1)).obj.left)
  let eL : S.X₁ ≅ A := horizontalCompleteFiltrationCochainMonoLowerSuccIso K p
  let eU : S.X₂ ≅ B := horizontalCompleteFiltrationCochainMonoUpperSuccIso K p
  let sL : A ≅ T.X₁ := horizontalNaturalStageCochainIso K p
  let sU : B ≅ T.X₂ := horizontalNaturalStageCochainIso K (p + 1)
  let e₀ : S.X₁ ≅ T.X₁ := eL ≪≫ sL
  let e₁ : S.X₂ ≅ T.X₂ := eU ≪≫ sU
  let e₂ : S.X₃ ≅ T.X₃ := Iso.refl _
  let a : A ⟶ B := F.map
    ((horizontalTotalFiltration K).toMonoOver.map (homOfLE (Nat.le_succ p))).hom.left
  have hnatural : a ≫ sU.hom = sL.hom ≫ T.f :=
    horizontalNaturalStageCochainIso_naturality K (Nat.le_succ p)
  have hmono : S.f ≫ eU.hom = eL.hom ≫ a :=
    horizontalFirstPageFiltrationMap_succ_monoIso K p
  refine ShortComplex.isoMk e₀ e₁ e₂ ?_ ?_
  · change (eL.hom ≫ sL.hom) ≫ T.f = S.f ≫ (eU.hom ≫ sU.hom)
    calc
      (eL.hom ≫ sL.hom) ≫ T.f = eL.hom ≫ (sL.hom ≫ T.f) :=
        Category.assoc _ _ _
      _ = eL.hom ≫ (a ≫ sU.hom) :=
        congrArg (fun f : A ⟶ T.X₂ => eL.hom ≫ f) hnatural.symm
      _ = (eL.hom ≫ a) ≫ sU.hom := (Category.assoc _ _ _).symm
      _ = (S.f ≫ eU.hom) ≫ sU.hom :=
        congrArg (fun f : S.X₁ ⟶ B => f ≫ sU.hom) hmono.symm
      _ = S.f ≫ (eU.hom ≫ sU.hom) := Category.assoc _ _ _
  · change (eU.hom ≫ sU.hom) ≫
        horizontalNaturalDirectColumnProjectionMap K (p + 1) =
      horizontalCompleteDirectColumnProjectionMap K (p + 1) ≫ 𝟙 _
    dsimp only [horizontalCompleteDirectColumnProjectionMap,
      horizontalCompleteSuccDirectColumnProjectionMap,
      horizontalMonoStageDirectColumnProjectionMap]
    simp only [Category.comp_id]
    dsimp only [eU, sU]
    exact Category.assoc _ _ _

/-- The inclusion of a finite filtration stage's top column.

Include bidegree `(p,q)` into stage `p` at total degree `p+q`. -/
noncomputable def horizontalFilteredTopInclusion (p q : ℕ) :
    (K.X p).X q ⟶ horizontalFilteredTotalObj K p (p + q) :=
  horizontalFilteredTotalι K p (p + q)
    (horizontalFilteredTopIndex p q)

/-- The unique-column projection at filtration stage zero.

Stage zero contains only bidegree `(0,q)` in total degree `q`, so top projection and inclusion
are inverse isomorphisms. -/
noncomputable def horizontalFilteredTopProjectionZeroIso (q : ℕ) :
    horizontalFilteredTotalObj K 0 (0 + q) ≅ (K.X 0).X q where
  hom := horizontalFilteredTopProjection K 0 q
  inv := horizontalFilteredTopInclusion K 0 q
  hom_inv_id := by
    have hFiber (F : DownNatHorizontalFilteredFiber (0 + q) 0 → C) :
        Sigma.π F (horizontalFilteredTopIndex 0 q) ≫
          Sigma.ι F (horizontalFilteredTopIndex 0 q) = 𝟙 (∐ F) := by
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
      rw [← Category.assoc, Sigma.ι_π]
      simp only [dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact hFiber (fun pq : DownNatHorizontalFilteredFiber (0 + q) 0 =>
      (K.X pq.val.val.1).X pq.val.val.2)
  inv_hom_id := by
    simpa [horizontalFilteredTopInclusion, horizontalFilteredTopIndex] using
      horizontalFilteredTopι_topProjection K 0 q

/-- The zero-column projection isomorphism in a supported degree.

At cochain degree `-q`, the complete zero-stage projection onto direct column zero is an
isomorphism. -/
theorem horizontalCompleteDirectColumnProjectionMap_zero_f_isIso_of_degree
    (q : ℕ) :
    IsIso ((horizontalCompleteDirectColumnProjectionMap K 0).f
      (-(0 : ℤ) - q)) := by
  change IsIso (horizontalDirectColumnProjection K 0 (-(0 : ℤ) - q))
  unfold horizontalDirectColumnProjection
  rw [dite_eq_left
    (show -(0 : ℤ) - (q : ℤ) ≤ -((0 : ℕ) : ℤ) by omega)]
  let q' := horizontalColumnDegree 0 (-(0 : ℤ) - (q : ℤ))
  let eTop : horizontalFilteredTotalObj K 0 (0 + q') ≅ (K.X 0).X q' :=
    horizontalFilteredTopProjectionZeroIso K q'
  have hTopHom : eTop.hom = horizontalFilteredTopProjection K 0 q' := rfl
  have htop : IsIso (horizontalFilteredTopProjection K 0 q') :=
    hTopHom ▸ eTop.isIso_hom
  let e₂ := horizontalDirectColumnCochainXIso K 0 q'
  have hcomp : IsIso (horizontalFilteredTopProjection K 0 q' ≫ e₂.inv) :=
    IsIso.comp_isIso'
      (f := horizontalFilteredTopProjection K 0 q') (h := e₂.inv)
      htop e₂.isIso_inv
  let n' : ℤ := -(0 : ℤ) - (q' : ℤ)
  let e₀ := (HomologicalComplex.eval C (ComplexShape.up ℤ) n').mapIso
    (horizontalCompleteFiltrationCochainUpperIso K 0)
  let e₁ := (horizontalFilteredTotalComplex K 0).extendXIso
    ComplexShape.embeddingDownNat (i := 0 + q') (i' := n') (by dsimp [n']; simp)
  have hcomponent : IsIso (horizontalDirectColumnProjectionComponent K 0 q') := by
    change IsIso
      (e₀.hom ≫ e₁.hom ≫ (horizontalFilteredTopProjection K 0 q' ≫ e₂.inv))
    exact IsIso.comp_isIso'
      (f := e₀.hom) (h := e₁.hom ≫ (horizontalFilteredTopProjection K 0 q' ≫ e₂.inv))
      e₀.isIso_hom
      (IsIso.comp_isIso'
        (f := e₁.hom) (h := horizontalFilteredTopProjection K 0 q' ≫ e₂.inv)
        e₁.isIso_hom hcomp)
  letI : IsIso (horizontalDirectColumnProjectionComponent K 0 q') := hcomponent
  infer_instance

/-- The zero-column projection isomorphism in every cochain degree.

All components of the complete projection onto direct column zero are isomorphisms, including
the zero objects above degree zero. -/
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

/-- Short exactness of natural consecutive-stage cochain sequences.

In an abelian category, the degreewise split natural filtration sequence is short exact as a
cochain-complex sequence. -/
theorem horizontalNaturalSuccCochainShortExact (p : ℕ) :
    (horizontalNaturalSuccCochainShortComplex K p).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact (horizontalNaturalSuccCochainEvalSplitting K p i).shortExact

/-- Short exactness of positive-column complete filtration sequences.

The complete-filtration sequence for column `p+1` is short exact through its natural-stage
comparison. -/
theorem horizontalFirstPageSuccShortExact (p : ℕ) :
    (horizontalFirstPageDirectColumnShortComplex K (p + 1)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (horizontalFirstPageSuccShortComplexIso K p).symm
    (horizontalNaturalSuccCochainShortExact K p)

/-- Short exactness of the zero-column complete filtration sequence.

The lower stage is zero and the direct-column projection is an isomorphism, giving a short
exact sequence in column zero. -/
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

/-- Short exactness of all complete filtration column sequences.

For every `p ≥ 0`, the consecutive-stage map and direct-column projection form a short exact
sequence. -/
theorem horizontalFirstPageDirectColumnShortExact (p : ℕ) :
    (horizontalFirstPageDirectColumnShortComplex K p).ShortExact := by
  cases p with
  | zero => exact horizontalFirstPageZeroShortExact K
  | succ p => exact horizontalFirstPageSuccShortExact K p

/-- The cokernel property of a complete direct-column projection.

The direct-column projection is a colimit cofork for the consecutive complete-filtration stage
map. -/
noncomputable def horizontalCompleteDirectColumnProjectionMapIsCokernel
    (p : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (horizontalCompleteDirectColumnProjectionMap K p)
      (horizontalFirstPageFiltrationMap_projection_zero K p)) :=
  (horizontalFirstPageDirectColumnShortExact K p).gIsCokernel

/-- The universal cokernel comparison with a direct shifted column.

The categorical cokernel and the direct-column cokernel cofork are canonically isomorphic by
their colimit universal properties. -/
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

/-- The forward factor of the universal graded-piece cokernel comparison.

The forward map of the universal cokernel isomorphism is the specified cokernel factor to the
direct column. -/
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

/-- The canonical direct-column cokernel isomorphism.

The cokernel of the first-page filtration map is isomorphic to the direct column, with forward
map the canonical projection factor and inverse from the universal cokernel comparison. -/
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

/-- The isomorphism property of the direct-column cokernel factor.

The specified factor from the consecutive-stage cokernel to the direct column is an
isomorphism. -/
noncomputable instance horizontalFirstPageCokernelToDirectColumn_isIso
    (p : ℕ) : IsIso (horizontalFirstPageCokernelToDirectColumn K p) :=
  (horizontalFirstPageCokernelIso K p).isIso_hom

end HomologicalComplex₂

end
