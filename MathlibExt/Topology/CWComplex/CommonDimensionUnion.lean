/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.CommonSuccessorSystem
import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization.ClassicalCellEmbedding
import MathlibExt.Topology.CWComplex.MatchedAmalgam
import MathlibExt.Topology.Category.TopCat.Colimits.FilteredClosedColimit
import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization
import MathlibExt.AlgebraicTopology.SimplicialComplex.MappingCylinder
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Actual common CW dimension union

`commonDimensionUnion` constructs the ordinary common-stage colimit from the
original Hausdorff CW space. The resulting data includes its Hausdorff CW
structure, closed stage subcomplexes, the global polyhedral realization
homeomorphism, both closed ends and their canonical characteristic cell maps.
-/



/-!
Construction of the actual ordinary common colimit CW data.
Born cells retain the original stage characteristics, finite frontiers and
weak topology. The construction includes closed stage subcomplexes, whole
disk compatibility, Hausdorffness and both compatible global ends.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

universe u

namespace CommonUnionCWBirthPreparation

namespace BirthLabels

variable {C : ℕ → Type u} (δ : ∀ n, C n ↪ C (n + 1))

private abbrev Birth : Type u := C 0 ⊕ (Σ n, {a : C (n + 1) // a ∉ Set.range (δ n)})

private def birthStage : Birth δ → ℕ
  | Sum.inl _ => 0
  | Sum.inr ⟨n, _⟩ => n + 1

private def birthCell : (b : Birth δ) → C (birthStage δ b)
  | Sum.inl a => a
  | Sum.inr ⟨_, a⟩ => a.val

open Classical in
private def reindex : (n : ℕ) → C n → Birth δ
  | 0, a => Sum.inl a
  | n + 1, a =>
      if h : a ∈ Set.range (δ n) then reindex n (Classical.choose h)
      else Sum.inr ⟨n, ⟨a, h⟩⟩

private theorem reindex_step (n : ℕ) (a : C n) :
    reindex δ (n + 1) (δ n a) = reindex δ n a := by
  classical
  have h : δ n a ∈ Set.range (δ n) := Set.mem_range_self a
  have hc : Classical.choose h = a :=
    (δ n).injective (Classical.choose_spec h)
  simpa only [reindex, dite_eq_left h] using congrArg (reindex δ n) hc

private theorem reindex_birth (b : Birth δ) :
    reindex δ (birthStage δ b) (birthCell δ b) = b := by
  classical
  cases b with
  | inl a => rfl
  | inr b =>
      rcases b with ⟨n, a⟩
      simp only [birthStage, birthCell, reindex, dite_eq_right a.property]

private theorem birthStage_reindex_le (n : ℕ) (a : C n) :
    birthStage δ (reindex δ n a) ≤ n := by
  classical
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      by_cases h : a ∈ Set.range (δ n)
      · simpa only [reindex, dite_eq_left h] using
          (ih (Classical.choose h)).trans (Nat.le_succ n)
      · simp only [reindex, dite_eq_right h, birthStage]
        exact Nat.le_refl _

private theorem reindex_injective (n : ℕ) : Function.Injective (reindex δ n) := by
  classical
  induction n with
  | zero => exact Sum.inl_injective
  | succ n ih =>
      intro a b hab
      by_cases ha : a ∈ Set.range (δ n)
      · by_cases hb : b ∈ Set.range (δ n)
        · have hpre : reindex δ n (Classical.choose ha) =
              reindex δ n (Classical.choose hb) := by
            simpa only [reindex, dite_eq_left ha, dite_eq_left hb] using hab
          calc
            a = δ n (Classical.choose ha) := (Classical.choose_spec ha).symm
            _ = δ n (Classical.choose hb) := congrArg (δ n) (ih hpre)
            _ = b := Classical.choose_spec hb
        · have hpre : reindex δ n (Classical.choose ha) =
              (Sum.inr ⟨n, ⟨b, hb⟩⟩ : Birth δ) := by
            simpa only [reindex, dite_eq_left ha, dite_eq_right hb] using hab
          have hstage := congrArg (birthStage δ) hpre
          have hle := birthStage_reindex_le δ n (Classical.choose ha)
          change birthStage δ (reindex δ n (Classical.choose ha)) = n + 1 at hstage
          omega
      · by_cases hb : b ∈ Set.range (δ n)
        · have hpre : (Sum.inr ⟨n, ⟨a, ha⟩⟩ : Birth δ) =
              reindex δ n (Classical.choose hb) := by
            simpa only [reindex, dite_eq_right ha, dite_eq_left hb] using hab
          have hstage := congrArg (birthStage δ) hpre
          have hle := birthStage_reindex_le δ n (Classical.choose hb)
          change n + 1 = birthStage δ (reindex δ n (Classical.choose hb)) at hstage
          omega
        · have hs : (⟨n, ⟨a, ha⟩⟩ : Σ n, {a : C (n + 1) // a ∉ Set.range (δ n)}) =
              ⟨n, ⟨b, hb⟩⟩ := by
            apply Sum.inr.inj
            simpa only [reindex, dite_eq_right ha, dite_eq_right hb] using hab
          exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp hs).2)

end BirthLabels

variable {X : TopCat.{u}} [T2Space X] [CWComplex (Set.univ : Set X)]
variable (S : CommonSuccessorSystemData X)

private def stageCell (n m : ℕ) : Type u :=
  letI := (S.stages n).cw
  cell (Set.univ : Set (S.stages n).space) m

private def cellStep (n m : ℕ) : stageCell S n m ↪ stageCell S (n + 1) m := by
  letI := (S.stages n).cw
  letI := (S.stages (n + 1)).cw
  exact S.oldStageLabels n m

private abbrev unionCell (m : ℕ) : Type u :=
  BirthLabels.Birth (fun n => cellStep S n m)

private def stageCellIntoUnion (n m : ℕ) : stageCell S n m ↪ unionCell S m :=
  ⟨BirthLabels.reindex (fun n => cellStep S n m) n,
    BirthLabels.reindex_injective (fun n => cellStep S n m) n⟩

private theorem stageCellIntoUnion_step (n m : ℕ) (a : stageCell S n m) :
    stageCellIntoUnion S (n + 1) m (cellStep S n m a) = stageCellIntoUnion S n m a :=
  BirthLabels.reindex_step (fun n => cellStep S n m) n a

private def commonSequence : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence (X := fun n => (S.stages n).space)
    (fun n => TopCat.ofHom (S.transition n))

private def diskFromStage (c : Cocone (commonSequence S)) (n m : ℕ)
    (a : stageCell S n m) : (classicalCellDiskPair.{u} m).fst ⟶ c.pt := by
  letI := (S.stages n).cw
  exact characteristicDiskMap (X := (S.stages n).space) m a ≫ c.ι.app n

private theorem diskFromStage_step (c : Cocone (commonSequence S)) (n m : ℕ)
    (a : stageCell S n m) :
    diskFromStage S c (n + 1) m (cellStep S n m a) = diskFromStage S c n m a := by
  let := (S.stages n).cw
  let := (S.stages (n + 1)).cw
  have hchar : characteristicDiskMap (X := (S.stages n).space) m a ≫
      TopCat.ofHom (S.transition n) =
      characteristicDiskMap (X := (S.stages (n + 1)).space) m (cellStep S n m a) :=
    S.oldStage_characteristicDiskMap n m a
  have hw : TopCat.ofHom (S.transition n) ≫ c.ι.app (n + 1) = c.ι.app n := by
    have hw₀ := c.w (homOfLE (Nat.le_add_right n 1))
    change (commonSequence S).map (homOfLE (Nat.le_add_right n 1)) ≫
      c.ι.app (n + 1) = c.ι.app n at hw₀
    simpa only [commonSequence, Functor.ofSequence_map_homOfLE_succ] using! hw₀
  change characteristicDiskMap (X := (S.stages (n + 1)).space) m (cellStep S n m a) ≫
      c.ι.app (n + 1) = characteristicDiskMap (X := (S.stages n).space) m a ≫ c.ι.app n
  calc
    _ = (characteristicDiskMap (X := (S.stages n).space) m a ≫
        TopCat.ofHom (S.transition n)) ≫ c.ι.app (n + 1) :=
      congrArg (fun f => f ≫ c.ι.app (n + 1)) hchar.symm
    _ = characteristicDiskMap (X := (S.stages n).space) m a ≫
        (TopCat.ofHom (S.transition n) ≫ c.ι.app (n + 1)) := Category.assoc _ _ _
    _ = characteristicDiskMap (X := (S.stages n).space) m a ≫ c.ι.app n :=
      congrArg (fun f => characteristicDiskMap (X := (S.stages n).space) m a ≫ f) hw

private def birthDisk (c : Cocone (commonSequence S)) (m : ℕ) :
    unionCell S m → ((classicalCellDiskPair.{u} m).fst ⟶ c.pt)
  | Sum.inl a => diskFromStage S c 0 m a
  | Sum.inr ⟨n, a⟩ => diskFromStage S c (n + 1) m a.val

private theorem birthDisk_stageCell (c : Cocone (commonSequence S)) (n m : ℕ)
    (a : stageCell S n m) :
    birthDisk S c m (stageCellIntoUnion S n m a) = diskFromStage S c n m a := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases ha : a ∈ Set.range (cellStep S n m)
      · have hstep : cellStep S n m (Classical.choose ha) = a := Classical.choose_spec ha
        calc
          _ = birthDisk S c m
              (BirthLabels.reindex (fun n => cellStep S n m) n (Classical.choose ha)) := by
            change birthDisk S c m
                (BirthLabels.reindex (fun n => cellStep S n m) (n + 1) a) = _
            rw [BirthLabels.reindex, dite_eq_left ha]
          _ = diskFromStage S c n m (Classical.choose ha) := ih (Classical.choose ha)
          _ = diskFromStage S c (n + 1) m (cellStep S n m (Classical.choose ha)) :=
            (diskFromStage_step S c n m (Classical.choose ha)).symm
          _ = diskFromStage S c (n + 1) m a := congrArg (diskFromStage S c (n + 1) m) hstep
      · change birthDisk S c m
          (BirthLabels.reindex (fun n => cellStep S n m) (n + 1) a) = _
        rw [BirthLabels.reindex, dite_eq_right ha]
        rfl


-- Arbitrary cell sets, including empty and infinite sets, retain injective stage labels.
example (n m : ℕ) : Function.Injective (stageCellIntoUnion S n m) :=
  (stageCellIntoUnion S n m).injective

-- The actual old-stage label is the same union label at the next stage.
example (n m : ℕ) (a : stageCell S n m) :
    stageCellIntoUnion S (n + 1) m (cellStep S n m a) = stageCellIntoUnion S n m a :=
  stageCellIntoUnion_step S n m a

-- Every birth is genuinely represented by its original stage and cell.
example (m : ℕ) (a : unionCell S m) :
    BirthLabels.reindex (fun n => cellStep S n m)
      (BirthLabels.birthStage (fun n => cellStep S n m) a)
      (BirthLabels.birthCell (fun n => cellStep S n m) a) = a :=
  BirthLabels.reindex_birth (fun n => cellStep S n m) a

-- The complete original closed-disk map is independent of its stage representative.
example (c : Cocone (commonSequence S)) (n m : ℕ) (a : stageCell S n m) :
    birthDisk S c m (stageCellIntoUnion S n m a) = diskFromStage S c n m a :=
  birthDisk_stageCell S c n m a

-- A separately chosen point of the entire literal closed disk uses the same map.
example (c : Cocone (commonSequence S)) (n m : ℕ) (a : stageCell S n m)
    (q : (classicalCellDiskPair.{u} m).fst) :
    letI := (S.stages n).cw
    birthDisk S c m (stageCellIntoUnion S n m a) q =
      c.ι.app n (characteristicDiskMap (X := (S.stages n).space) m a q) := by
  let := (S.stages n).cw
  exact (ConcreteCategory.congr_hom (birthDisk_stageCell S c n m a) q).trans
    (ConcreteCategory.comp_apply _ _ q)

end CommonUnionCWBirthPreparation

end


/- The actual ordinary colimit CW record. The later construction supplies
Hausdorffness and the global polyhedral-end realization homeomorphism. -/
noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

universe u

namespace CommonUnionCWBirthPreparation

namespace BirthLabels

variable {C : ℕ → Type u} (δ : ∀ n, C n ↪ C (n + 1))

private theorem representedAt (b : Birth δ) (n : ℕ) (hn : birthStage δ b ≤ n) :
    ∃ a : C n, reindex δ n a = b := by
  induction n generalizing b with
  | zero =>
      cases b with
      | inl a => exact ⟨a, rfl⟩
      | inr b =>
          rcases b with ⟨k, a⟩
          change k + 1 ≤ 0 at hn
          omega
  | succ n ih =>
      by_cases h : birthStage δ b ≤ n
      · obtain ⟨a, ha⟩ := ih b h
        exact ⟨δ n a, (reindex_step δ n a).trans ha⟩
      · cases b with
        | inl a =>
            have h0 : birthStage δ (Sum.inl a) ≤ n := by
              change 0 ≤ n
              omega
            exact (h h0).elim
        | inr b =>
            rcases b with ⟨k, a⟩
            change k + 1 ≤ n + 1 at hn
            change ¬ k + 1 ≤ n at h
            have hk : k = n := by omega
            subst k
            exact ⟨a.val, reindex_birth δ (Sum.inr ⟨n, a⟩)⟩

end BirthLabels

variable {X : TopCat.{u}} [T2Space X] [CWComplex (Set.univ : Set X)]
variable (S : CommonSuccessorSystemData X)

private theorem sequenceMap_closed (i j : ℕ) (hij : i ≤ j) :
    IsClosedEmbedding ((commonSequence S).map (homOfLE hij)).hom := by
  induction j, hij using Nat.le_induction with
  | base =>
      have hid : (commonSequence S).map (homOfLE (le_refl i)) =
          𝟙 ((commonSequence S).obj i) := (commonSequence S).map_id i
      rw [hid]
      exact IsClosedEmbedding.id
  | succ j hij ih =>
      have he : homOfLE (hij.trans (Nat.le_succ j)) =
          homOfLE hij ≫ homOfLE (Nat.le_succ j) := rfl
      rw [he, Functor.map_comp]
      have hs : ((commonSequence S).map (homOfLE (Nat.le_succ j))).hom =
          S.transition j := by
        simp only [commonSequence, Functor.ofSequence_map_homOfLE_succ]
        rfl
      simpa only [TopCat.hom_comp, ContinuousMap.coe_comp, hs] using!
        (S.transition_closed j).comp ih

private theorem sequenceAllMaps_closed {i j : ℕ} (f : i ⟶ j) :
    IsClosedEmbedding ((commonSequence S).map f).hom := by
  have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  exact hf ▸ sequenceMap_closed S i j (leOfHom f)

private abbrev unionSpace : TopCat.{u} := colimit (commonSequence S)

private def unionCocone : Cocone (commonSequence S) := colimit.cocone (commonSequence S)

private def unionCocone_isColimit : IsColimit (unionCocone S) :=
  colimit.isColimit (commonSequence S)

private def unionLeg (n : ℕ) : (S.stages n).space ⟶ unionSpace S :=
  (unionCocone S).ι.app n

private theorem unionLeg_closed (n : ℕ) : IsClosedEmbedding (unionLeg S n).hom :=
  TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding
    (unionCocone S) (unionCocone_isColimit S) (fun _ _ f => sequenceAllMaps_closed S f) n

private abbrev unionBirthStage (m : ℕ) (b : unionCell S m) :=
  BirthLabels.birthStage (fun n => cellStep S n m) b

private def unionBirthCell (m : ℕ) (b : unionCell S m) :
    stageCell S (unionBirthStage S m b) m :=
  BirthLabels.birthCell (fun n => cellStep S n m) b

private theorem unionCell_represented (m : ℕ) (b : unionCell S m) (n : ℕ)
    (hn : unionBirthStage S m b ≤ n) :
    ∃ a : stageCell S n m, stageCellIntoUnion S n m a = b :=
  BirthLabels.representedAt (fun n => cellStep S n m) b n hn

private def unionCellTotal (m : ℕ) (b : unionCell S m) : (Fin m → ℝ) → unionSpace S := by
  letI := (S.stages (unionBirthStage S m b)).cw
  exact fun x => unionLeg S (unionBirthStage S m b)
    (map (C := (Set.univ : Set (S.stages (unionBirthStage S m b)).space)) m
      (unionBirthCell S m b) x)

private theorem unionCellTotal_disk (m : ℕ) (b : unionCell S m)
    (q : (classicalCellDiskPair.{u} m).fst) :
    unionCellTotal S m b q.down.val = birthDisk S (unionCocone S) m b q := by
  cases b with
  | inl a => rfl
  | inr b =>
      rcases b with ⟨n, a⟩
      rfl

private theorem unionCellTotal_stage (n m : ℕ) (a : stageCell S n m)
    (x : Fin m → ℝ) (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) 1) :
    letI := (S.stages n).cw
    unionCellTotal S m (stageCellIntoUnion S n m a) x =
      unionLeg S n (map (C := (Set.univ : Set (S.stages n).space)) m a x) := by
  let := (S.stages n).cw
  let q : (classicalCellDiskPair.{u} m).fst := ULift.up ⟨x, hx⟩
  have h₁ : unionCellTotal S m (stageCellIntoUnion S n m a) x =
      birthDisk S (unionCocone S) m (stageCellIntoUnion S n m a) q :=
    unionCellTotal_disk S m (stageCellIntoUnion S n m a) q
  have h₂ : birthDisk S (unionCocone S) m (stageCellIntoUnion S n m a) q =
      diskFromStage S (unionCocone S) n m a q :=
    ConcreteCategory.congr_hom (birthDisk_stageCell S (unionCocone S) n m a) q
  exact h₁.trans h₂

private theorem unionCellTotal_stage_image (n m : ℕ) (a : stageCell S n m)
    (K : Set (Fin m → ℝ)) (hK : K ⊆ Metric.closedBall (0 : Fin m → ℝ) 1) :
    letI := (S.stages n).cw
    unionCellTotal S m (stageCellIntoUnion S n m a) '' K =
      unionLeg S n '' (map (C := (Set.univ : Set (S.stages n).space)) m a '' K) := by
  let := (S.stages n).cw
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨map (C := (Set.univ : Set (S.stages n).space)) m a x, ⟨x, hx, rfl⟩,
      (unionCellTotal_stage S n m a x (hK hx)).symm.trans hxy⟩
  · rintro ⟨z, ⟨x, hx, hxz⟩, hzy⟩
    exact ⟨x, hx, (unionCellTotal_stage S n m a x (hK hx)).trans
      ((congrArg (unionLeg S n) hxz).trans hzy)⟩

private theorem unionCellTotal_openEmbedding (m : ℕ) (b : unionCell S m) :
    IsEmbedding (fun x : Metric.ball (0 : Fin m → ℝ) 1 => unionCellTotal S m b x.val) := by
  let := (S.stages (unionBirthStage S m b)).cw
  exact (unionLeg_closed S (unionBirthStage S m b)).isEmbedding.comp
    (MatchedAmalgam.openCellMap_isEmbedding m (unionBirthCell S m b))

private def unionCellPartial (m : ℕ) (b : unionCell S m) :
    PartialEquiv (Fin m → ℝ) (unionSpace S) :=
  MatchedAmalgam.cellPartialEquivOfEmbedding m (unionCellTotal S m b)
    (unionCellTotal_openEmbedding S m b)

private theorem unionCellPartial_apply (m : ℕ) (b : unionCell S m) (x : Fin m → ℝ) :
    unionCellPartial S m b x = unionCellTotal S m b x :=
  MatchedAmalgam.cellPartialEquivOfEmbedding_apply m (unionCellTotal S m b)
    (unionCellTotal_openEmbedding S m b) x

private theorem unionCellPartial_toFun (m : ℕ) (b : unionCell S m) :
    (unionCellPartial S m b : (Fin m → ℝ) → unionSpace S) = unionCellTotal S m b :=
  funext (unionCellPartial_apply S m b)

private theorem unionCellPartial_source (m : ℕ) (b : unionCell S m) :
    (unionCellPartial S m b).source = Metric.ball (0 : Fin m → ℝ) 1 :=
  MatchedAmalgam.cellPartialEquivOfEmbedding_source m (unionCellTotal S m b)
    (unionCellTotal_openEmbedding S m b)

private theorem unionCellPartial_continuousOn (m : ℕ) (b : unionCell S m) :
    ContinuousOn (unionCellPartial S m b) (Metric.closedBall (0 : Fin m → ℝ) 1) := by
  let := (S.stages (unionBirthStage S m b)).cw
  rw [unionCellPartial_toFun]
  exact (unionLeg S (unionBirthStage S m b)).hom.continuous.comp_continuousOn
    (continuousOn (C := (Set.univ : Set (S.stages (unionBirthStage S m b)).space)) m
      (unionBirthCell S m b))

private theorem unionCellPartial_inverseContinuous (m : ℕ) (b : unionCell S m) :
    ContinuousOn (unionCellPartial S m b).symm (unionCellPartial S m b).target :=
  MatchedAmalgam.cellPartialEquivOfEmbedding_continuousOn_symm m (unionCellTotal S m b)
    (unionCellTotal_openEmbedding S m b)

private theorem unionCellTotal_pairwiseDisjoint :
    (Set.univ : Set (Σ m, unionCell S m)).PairwiseDisjoint
      (fun b => unionCellTotal S b.fst b.snd '' Metric.ball 0 1) := by
  rintro ⟨m, b⟩ _ ⟨k, d⟩ _ hne
  let n := max (unionBirthStage S m b) (unionBirthStage S k d)
  obtain ⟨a, ha⟩ := unionCell_represented S m b n (le_max_left _ _)
  obtain ⟨c, hc⟩ := unionCell_represented S k d n (le_max_right _ _)
  let := (S.stages n).cw
  have hne' : (⟨m, a⟩ : Σ l, stageCell S n l) ≠ ⟨k, c⟩ := by
    intro heq
    have hout := congrArg
      (fun z : Σ l, stageCell S n l =>
        (⟨z.fst, stageCellIntoUnion S n z.fst z.snd⟩ : Σ l, unionCell S l)) heq
    exact hne (by simpa only [ha, hc] using hout)
  have hm := unionCellTotal_stage_image S n m a (Metric.ball 0 1)
    Metric.ball_subset_closedBall
  have hk := unionCellTotal_stage_image S n k c (Metric.ball 0 1)
    Metric.ball_subset_closedBall
  rw [ha] at hm
  rw [hc] at hk
  change Disjoint (unionCellTotal S m b '' Metric.ball 0 1)
    (unionCellTotal S k d '' Metric.ball 0 1)
  rw [hm, hk]
  exact Set.disjoint_image_of_injective (unionLeg_closed S n).injective
    (disjoint_openCell_of_ne (C := (Set.univ : Set (S.stages n).space)) hne')

private theorem unionCellTotal_frontier (m : ℕ) (b : unionCell S m) :
    ∃ I : ∀ l, Finset (unionCell S l),
      Set.MapsTo (unionCellTotal S m b) (Metric.sphere (0 : Fin m → ℝ) 1)
        (⋃ (l < m) (a ∈ I l), unionCellTotal S l a '' Metric.closedBall 0 1) := by
  classical
  let n := unionBirthStage S m b
  let := (S.stages n).cw
  obtain ⟨I, hI⟩ := CWComplex.mapsTo' (C := (Set.univ : Set (S.stages n).space)) m
    (unionBirthCell S m b)
  refine ⟨fun l => (I l).image (stageCellIntoUnion S n l), ?_⟩
  intro x hx
  have hsource := hI hx
  simp only [Set.mem_iUnion, Set.mem_image] at hsource ⊢
  rcases hsource with ⟨l, hl, a, ha, y, hy, heq⟩
  refine ⟨l, hl, stageCellIntoUnion S n l a,
    Finset.mem_image.mpr ⟨a, ha, rfl⟩, y, hy, ?_⟩
  calc
    unionCellTotal S l (stageCellIntoUnion S n l a) y =
        unionLeg S n (map (C := (Set.univ : Set (S.stages n).space)) l a y) :=
      unionCellTotal_stage S n l a y hy
    _ = unionLeg S n
        (map (C := (Set.univ : Set (S.stages n).space)) m (unionBirthCell S m b) x) :=
      congrArg (unionLeg S n) heq
    _ = unionCellTotal S m b x := rfl

private theorem unionCellTotal_weakClosed (A : Set (unionSpace S))
    (hA : ∀ m (b : unionCell S m),
      IsClosed (A ∩ unionCellTotal S m b '' Metric.closedBall 0 1)) : IsClosed A := by
  apply (TopCat.isClosed_iff_of_isColimit (unionCocone S) (unionCocone_isColimit S) A).mpr
  intro n
  let := (S.stages n).cw
  apply CWComplex.closed' (C := (Set.univ : Set (S.stages n).space)) _ (Set.subset_univ _)
  intro m a
  have himage := unionCellTotal_stage_image S n m a (Metric.closedBall 0 1) (Set.Subset.refl _)
  have hclosed := (hA m (stageCellIntoUnion S n m a)).preimage (unionLeg S n).hom.continuous
  rw [himage, Set.preimage_inter,
    Set.preimage_image_eq _ (unionLeg_closed S n).injective] at hclosed
  exact hclosed

private theorem unionCellTotal_union :
    (⋃ (m : ℕ) (b : unionCell S m), unionCellTotal S m b '' Metric.closedBall 0 1) =
      Set.univ := by
  ext y
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    obtain ⟨n, x, hxy⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget TopCat) (unionCocone_isColimit S)) y
    let := (S.stages n).cw
    let x₀ : (S.stages n).space := x
    have hx : x₀ ∈ ⋃ (m : ℕ)
        (a : cell (Set.univ : Set (S.stages n).space) m),
        map (C := (Set.univ : Set (S.stages n).space)) m a '' Metric.closedBall 0 1 := by
      have hcover := _root_.Topology.CWComplex.union' (C := (Set.univ : Set (S.stages n).space))
      have hmem : x₀ ∈ (Set.univ : Set (S.stages n).space) := Set.mem_univ _
      have hc := Eq.mpr (congrArg (fun A : Set (S.stages n).space => x₀ ∈ A) hcover) hmem
      simpa only [CWComplex.instRelCWComplex] using! hc
    simp only [Set.mem_iUnion, Set.mem_image] at hx ⊢
    rcases hx with ⟨m, a, q, hq, hqx⟩
    exact ⟨m, stageCellIntoUnion S n m a, q, hq,
      (unionCellTotal_stage S n m a q hq).trans
        ((congrArg (unionLeg S n) hqx).trans hxy)⟩

@[instance_reducible]
private def unionClassicalCW : CWComplex (Set.univ : Set (unionSpace S)) where
  cell := unionCell S
  map := unionCellPartial S
  source_eq := unionCellPartial_source S
  continuousOn := unionCellPartial_continuousOn S
  continuousOn_symm := unionCellPartial_inverseContinuous S
  pairwiseDisjoint' := by
    simpa only [unionCellPartial_toFun] using unionCellTotal_pairwiseDisjoint S
  mapsTo' := by
    simpa only [unionCellPartial_toFun] using unionCellTotal_frontier S
  closed' A _ hA := by
    apply unionCellTotal_weakClosed S A
    simpa only [unionCellPartial_toFun] using hA
  union' := by
    simpa only [unionCellPartial_toFun] using unionCellTotal_union S

private theorem unionCharacteristicDisk_stage (n m : ℕ) (a : stageCell S n m) :
    letI := unionClassicalCW S
    letI := (S.stages n).cw
    characteristicDiskMap (X := unionSpace S) m (stageCellIntoUnion S n m a) =
      characteristicDiskMap (X := (S.stages n).space) m a ≫ unionLeg S n := by
  let := unionClassicalCW S
  let := (S.stages n).cw
  apply TopCat.ext
  intro q
  change unionCellPartial S m (stageCellIntoUnion S n m a) q.down.val = _
  exact (unionCellPartial_apply S m (stageCellIntoUnion S n m a) q.down.val).trans
    (unionCellTotal_stage S n m a q.down.val q.down.property)

private def unionStageSubcomplex (n : ℕ) :
    letI := unionClassicalCW S
    Subcomplex (Set.univ : Set (unionSpace S)) := by
  letI := unionClassicalCW S
  letI := (S.stages n).cw
  refine
    { carrier := Set.range (unionLeg S n)
      I := fun m => Set.range (stageCellIntoUnion S n m)
      closed' := (unionLeg_closed S n).isClosed_range
      union' := ?_ }
  rw [Set.empty_union]
  ext y
  constructor
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨m, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨a, ha⟩
    rcases a.property with ⟨b, hb⟩
    rcases ha with ⟨q, hq, hqy⟩
    have heval := unionCellTotal_stage S n m b q (Metric.ball_subset_closedBall hq)
    change unionCellPartial S m a.val q = y at hqy
    rw [unionCellPartial_apply, ← hb] at hqy
    exact ⟨map (C := (Set.univ : Set (S.stages n).space)) m b q,
      heval.symm.trans hqy⟩
  · rintro ⟨x, rfl⟩
    have hx : x ∈ ⋃ (m : ℕ)
        (a : cell (Set.univ : Set (S.stages n).space) m),
        openCell (C := (Set.univ : Set (S.stages n).space)) m a := by
      rw [iUnion_openCell_eq_complex]
      exact Set.mem_univ _
    rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨a, ha⟩
    rcases ha with ⟨q, hq, hqx⟩
    refine Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
      ⟨⟨stageCellIntoUnion S n m a, ⟨a, rfl⟩⟩, ?_⟩⟩
    refine ⟨q, hq, ?_⟩
    change unionCellPartial S m (stageCellIntoUnion S n m a) q = unionLeg S n x
    exact (unionCellPartial_apply S m (stageCellIntoUnion S n m a) q).trans
      ((unionCellTotal_stage S n m a q (Metric.ball_subset_closedBall hq)).trans
        (congrArg (unionLeg S n) hqx))

private theorem unionStageSubcomplex_carrier (n : ℕ) :
    letI := unionClassicalCW S
    (unionStageSubcomplex S n : Set (unionSpace S)) = Set.range (unionLeg S n) := rfl

private theorem unionStageSubcomplex_labels (n m : ℕ) :
    letI := unionClassicalCW S
    (unionStageSubcomplex S n).I m = Set.range (stageCellIntoUnion S n m) := rfl

@[instance_reducible]
private def actualOriginalXUnionCW (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] :
    CWComplex (Set.univ : Set (unionSpace (commonSuccessorSystem X))) :=
  unionClassicalCW (commonSuccessorSystem X)


example : CWComplex (Set.univ : Set (unionSpace S)) := unionClassicalCW S

example (n m : ℕ) (a : stageCell S n m) :
    letI := unionClassicalCW S
    letI := (S.stages n).cw
    characteristicDiskMap (X := unionSpace S) m (stageCellIntoUnion S n m a) =
      characteristicDiskMap (X := (S.stages n).space) m a ≫ unionLeg S n :=
  unionCharacteristicDisk_stage S n m a

example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :
    CWComplex (Set.univ : Set (unionSpace (commonSuccessorSystem X))) :=
  actualOriginalXUnionCW X

end CommonUnionCWBirthPreparation

end


/- Hausdorffness from actual trace-preserving open-pair extensions. -/
noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

universe u

namespace CommonUnionCWBirthPreparation
namespace HausdorffUnion

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

private structure StageOpenPair (n : ℕ) where
  U : Set ((commonSuccessorSystem X).stages n).space
  V : Set ((commonSuccessorSystem X).stages n).space
  openU : IsOpen U
  openV : IsOpen V
  disjoint : Disjoint U V

private def extendStageOpenPair {n : ℕ} (p : StageOpenPair X n) :
    {q : StageOpenPair X (n + 1) //
      (commonSuccessorSystem X).transition n ⁻¹' q.U = p.U ∧
      (commonSuccessorSystem X).transition n ⁻¹' q.V = p.V} := by
  classical
  let h := commonSuccessorSystem_transition_disjointOpenExtension X n
    p.U p.V p.openU p.openV p.disjoint
  let U := Classical.choose h
  let hU := Classical.choose_spec h
  let V := Classical.choose hU
  let hV := Classical.choose_spec hU
  exact ⟨⟨U, V, hV.1, hV.2.1, hV.2.2.1⟩, hV.2.2.2.1, hV.2.2.2.2⟩

private def pairTail (N : ℕ) (p : StageOpenPair X N) :
    (k : ℕ) → StageOpenPair X (N + k)
  | 0 => p
  | k + 1 => (extendStageOpenPair X (pairTail N p k)).val

private theorem pairTail_step (N : ℕ) (p : StageOpenPair X N) (k : ℕ) :
    (commonSuccessorSystem X).transition (N + k) ⁻¹' (pairTail X N p (k + 1)).U =
        (pairTail X N p k).U ∧
    (commonSuccessorSystem X).transition (N + k) ⁻¹' (pairTail X N p (k + 1)).V =
        (pairTail X N p k).V :=
  (extendStageOpenPair X (pairTail X N p k)).property

private def pairSide {n : ℕ} (p : StageOpenPair X n) (left : Bool) :
    Set ((commonSuccessorSystem X).stages n).space :=
  if left then p.U else p.V

private theorem pairSide_open {n : ℕ} (p : StageOpenPair X n) (left : Bool) :
    IsOpen (pairSide X p left) := by
  cases left with
  | false => exact p.openV
  | true => exact p.openU

private theorem pairTail_stepSide (N : ℕ) (p : StageOpenPair X N) (k : ℕ) (left : Bool) :
    (commonSuccessorSystem X).transition (N + k) ⁻¹'
        pairSide X (pairTail X N p (k + 1)) left =
      pairSide X (pairTail X N p k) left := by
  cases left with
  | false => exact (pairTail_step X N p k).2
  | true => exact (pairTail_step X N p k).1

private def tailMap (N i j : ℕ) (h : i ≤ j) :
    ((commonSuccessorSystem X).stages (N + i)).space ⟶
      ((commonSuccessorSystem X).stages (N + j)).space :=
  (commonSequence (commonSuccessorSystem X)).map (homOfLE (Nat.add_le_add_left h N))

private theorem tailMap_id (N i : ℕ) :
    tailMap X N i i (Nat.le_refl i) = 𝟙 _ := by
  unfold tailMap
  have h : (homOfLE (Nat.add_le_add_left (Nat.le_refl i) N) : N + i ⟶ N + i) =
      𝟙 (N + i) := Subsingleton.elim _ _
  exact (congrArg (commonSequence (commonSuccessorSystem X)).map h).trans
    ((commonSequence (commonSuccessorSystem X)).map_id (N + i))

private theorem tailMap_succ (N k : ℕ) :
    tailMap X N k (k + 1) (Nat.le_succ k) =
      TopCat.ofHom ((commonSuccessorSystem X).transition (N + k)) := by
  simp only [tailMap, commonSequence, Functor.ofSequence_map_homOfLE_succ]

private theorem tailMap_comp (N i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    tailMap X N i k (hij.trans hjk) = tailMap X N i j hij ≫ tailMap X N j k hjk := by
  let f : N + i ⟶ N + j := homOfLE (Nat.add_le_add_left hij N)
  let g : N + j ⟶ N + k := homOfLE (Nat.add_le_add_left hjk N)
  have h : (homOfLE (Nat.add_le_add_left (hij.trans hjk) N) : N + i ⟶ N + k) =
      f ≫ g := Subsingleton.elim _ _
  exact (congrArg (commonSequence (commonSuccessorSystem X)).map h).trans
    ((commonSequence (commonSuccessorSystem X)).map_comp f g)

private theorem pairTail_traceAdd (N : ℕ) (p : StageOpenPair X N) (i k : ℕ)
    (x : ((commonSuccessorSystem X).stages (N + i)).space) (left : Bool) :
    tailMap X N i (i + k) (Nat.le_add_right i k) x ∈
        pairSide X (pairTail X N p (i + k)) left ↔
      x ∈ pairSide X (pairTail X N p i) left := by
  induction k with
  | zero =>
      change tailMap X N i i (Nat.le_refl i) x ∈
        pairSide X (pairTail X N p i) left ↔ x ∈ pairSide X (pairTail X N p i) left
      have heq := ConcreteCategory.congr_hom (tailMap_id X N i) x
      exact iff_of_eq (congrArg (fun z => z ∈ pairSide X (pairTail X N p i) left) heq)
  | succ k ih =>
      change tailMap X N i (i + k + 1) (Nat.le_add_right i (k + 1)) x ∈
        pairSide X (pairTail X N p (i + k + 1)) left ↔ _
      have hc := ConcreteCategory.congr_hom
        (tailMap_comp X N i (i + k) (i + k + 1)
          (Nat.le_add_right i k) (Nat.le_succ (i + k))) x
      let y := tailMap X N i (i + k) (Nat.le_add_right i k) x
      have hs := ConcreteCategory.congr_hom (tailMap_succ X N (i + k)) y
      have heval : tailMap X N i (i + k + 1) (Nat.le_add_right i (k + 1)) x =
          (commonSuccessorSystem X).transition (N + (i + k)) y := hc.trans hs
      have ht : (commonSuccessorSystem X).transition (N + (i + k)) y ∈
          pairSide X (pairTail X N p (i + k + 1)) left ↔
            y ∈ pairSide X (pairTail X N p (i + k)) left :=
        iff_of_eq (congrArg (fun A : Set ((commonSuccessorSystem X).stages (N + (i + k))).space =>
          y ∈ A) (pairTail_stepSide X N p (i + k) left))
      exact (iff_of_eq (congrArg (fun z =>
          z ∈ pairSide X (pairTail X N p (i + k + 1)) left) heval)).trans (ht.trans ih)

private theorem pairTail_trace (N : ℕ) (p : StageOpenPair X N) (i j : ℕ) (hij : i ≤ j)
    (x : ((commonSuccessorSystem X).stages (N + i)).space) (left : Bool) :
    tailMap X N i j hij x ∈ pairSide X (pairTail X N p j) left ↔
      x ∈ pairSide X (pairTail X N p i) left := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact pairTail_traceAdd X N p i k x left

private theorem leg_map (i j : ℕ) (hij : i ≤ j)
    (x : ((commonSuccessorSystem X).stages i).space) :
    unionLeg (commonSuccessorSystem X) j
        ((commonSequence (commonSuccessorSystem X)).map (homOfLE hij) x) =
      unionLeg (commonSuccessorSystem X) i x :=
  ConcreteCategory.congr_hom ((unionCocone (commonSuccessorSystem X)).w (homOfLE hij)) x

private theorem tailLeg_map (N i j : ℕ) (hij : i ≤ j)
    (x : ((commonSuccessorSystem X).stages (N + i)).space) :
    unionLeg (commonSuccessorSystem X) (N + j) (tailMap X N i j hij x) =
      unionLeg (commonSuccessorSystem X) (N + i) x :=
  leg_map X (N + i) (N + j) (Nat.add_le_add_left hij N) x

private def globalTailOpen (N : ℕ) (p : StageOpenPair X N) (left : Bool) :
    Set (unionSpace (commonSuccessorSystem X)) :=
  ⋃ k, unionLeg (commonSuccessorSystem X) (N + k) ''
    pairSide X (pairTail X N p k) left

private theorem globalTailOpen_preimage (N : ℕ) (p : StageOpenPair X N)
    (left : Bool) (n : ℕ) :
    unionLeg (commonSuccessorSystem X) n ⁻¹' globalTailOpen X N p left =
      ((commonSequence (commonSuccessorSystem X)).map
        (homOfLE (show n ≤ N + n by omega))) ⁻¹'
          pairSide X (pairTail X N p n) left := by
  ext x
  let x₁ : ((commonSuccessorSystem X).stages (N + n)).space :=
    (commonSequence (commonSuccessorSystem X)).map
      (homOfLE (show n ≤ N + n by omega)) x
  constructor
  · intro hx
    change unionLeg (commonSuccessorSystem X) n x ∈
      ⋃ k, unionLeg (commonSuccessorSystem X) (N + k) ''
        pairSide X (pairTail X N p k) left at hx
    rcases Set.mem_iUnion.mp hx with ⟨k, y, hy, hxy⟩
    let m := max n k
    have hn : n ≤ m := le_max_left _ _
    have hk : k ≤ m := le_max_right _ _
    have heq : tailMap X N n m hn x₁ = tailMap X N k m hk y := by
      apply (unionLeg_closed (commonSuccessorSystem X) (N + m)).injective
      exact (tailLeg_map X N n m hn x₁).trans
        ((leg_map X n (N + n) (by omega) x).trans
          (hxy.symm.trans (tailLeg_map X N k m hk y).symm))
    have hup : tailMap X N k m hk y ∈ pairSide X (pairTail X N p m) left :=
      (pairTail_trace X N p k m hk y left).2 hy
    have hxn : x₁ ∈ pairSide X (pairTail X N p n) left :=
      (pairTail_trace X N p n m hn x₁ left).1 (by rw [heq]; exact hup)
    exact hxn
  · intro hx
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    exact ⟨x₁, hx, leg_map X n (N + n) (by omega) x⟩

private theorem globalTailOpen_isOpen (N : ℕ) (p : StageOpenPair X N) (left : Bool) :
    IsOpen (globalTailOpen X N p left) := by
  apply (TopCat.isOpen_iff_of_isColimit (unionCocone (commonSuccessorSystem X))
    (unionCocone_isColimit (commonSuccessorSystem X)) _).mpr
  intro n
  have hpre := globalTailOpen_preimage X N p left n
  have hopen := (pairSide_open X (pairTail X N p n) left).preimage
    ((commonSequence (commonSuccessorSystem X)).map
      (homOfLE (show n ≤ N + n by omega))).hom.continuous
  exact Eq.mpr (congrArg (fun A : Set ((commonSuccessorSystem X).stages n).space =>
    IsOpen A) hpre) hopen

private theorem globalTailOpen_disjoint (N : ℕ) (p : StageOpenPair X N) :
    Disjoint (globalTailOpen X N p true) (globalTailOpen X N p false) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  rcases Set.mem_iUnion.mp hz₁ with ⟨i, x, hx, hxz⟩
  rcases Set.mem_iUnion.mp hz₂ with ⟨j, y, hy, hyz⟩
  let k := max i j
  have hi : i ≤ k := le_max_left _ _
  have hj : j ≤ k := le_max_right _ _
  have heq : tailMap X N i k hi x = tailMap X N j k hj y := by
    apply (unionLeg_closed (commonSuccessorSystem X) (N + k)).injective
    exact (tailLeg_map X N i k hi x).trans
      ((hxz.trans hyz.symm).trans (tailLeg_map X N j k hj y).symm)
  have hU : tailMap X N i k hi x ∈ (pairTail X N p k).U :=
    (pairTail_trace X N p i k hi x true).2 hx
  have hV : tailMap X N j k hj y ∈ (pairTail X N p k).V :=
    (pairTail_trace X N p j k hj y false).2 hy
  exact (pairTail X N p k).disjoint.notMem_of_mem_left hU (heq.symm ▸ hV)

private theorem actualCommonUnionHausdorff : T2Space (unionSpace (commonSuccessorSystem X)) := by
  refine ⟨?_⟩
  intro x y hxy
  obtain ⟨N, a, b, hax, hby⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget TopCat)
      (unionCocone_isColimit (commonSuccessorSystem X))) x y
  have hab : a ≠ b := by
    intro h
    exact hxy (hax.symm.trans ((congrArg (unionLeg (commonSuccessorSystem X) N) h).trans hby))
  let := ((commonSuccessorSystem X).stages N).hausdorff
  let a₀ : ((commonSuccessorSystem X).stages N).space := a
  let b₀ : ((commonSuccessorSystem X).stages N).space := b
  have hab₀ : a₀ ≠ b₀ := hab
  obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := t2_separation hab₀
  let p : StageOpenPair X N := ⟨U, V, hU, hV, hUV⟩
  refine ⟨globalTailOpen X N p true, globalTailOpen X N p false,
    globalTailOpen_isOpen X N p true, globalTailOpen_isOpen X N p false,
    ?_, ?_, globalTailOpen_disjoint X N p⟩
  · exact Set.mem_iUnion.mpr ⟨0, ⟨a, ha, hax⟩⟩
  · exact Set.mem_iUnion.mpr ⟨0, ⟨b, hb, hby⟩⟩


example : T2Space (unionSpace (commonSuccessorSystem X)) := actualCommonUnionHausdorff X

example (N : ℕ) (p : StageOpenPair X N) :
    IsOpen (globalTailOpen X N p true) ∧ IsOpen (globalTailOpen X N p false) ∧
      Disjoint (globalTailOpen X N p true) (globalTailOpen X N p false) :=
  ⟨globalTailOpen_isOpen X N p true, globalTailOpen_isOpen X N p false,
    globalTailOpen_disjoint X N p⟩

example (N : ℕ) (p : StageOpenPair X N) (n : ℕ) :
    unionLeg (commonSuccessorSystem X) n ⁻¹' globalTailOpen X N p true =
      ((commonSequence (commonSuccessorSystem X)).map
        (homOfLE (show n ≤ N + n by omega))) ⁻¹'
          pairSide X (pairTail X N p n) true :=
  globalTailOpen_preimage X N p true n

end HausdorffUnion
end CommonUnionCWBirthPreparation

end




/-!
# The actual weak polyhedral end in the ordinary common dimension union

Both previously verified private constructions are colocated. The new end is
the inverse of the actual polyhedral colimit homeomorphism followed by the
original compatible common-union end map. No union CW, topology, comparison,
vertex matching, or inverse witness is a premise of this construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex

universe u

namespace ActualCommonDimensionUnionConstruction

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

private def commonSequence : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence (X := fun n => ((commonSuccessorSystem X).stages n).space)
    (fun n => TopCat.ofHom ((commonSuccessorSystem X).transition n))

private def originalSequence : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence (X := fun n => skeletonTop X (n + 1))
    (fun n => skeletonTransition X (n + 1))

private def polyhedralSequence : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence
    (X := fun n => TopCat.of (((commonSuccessorSystem X).stages n).polyhedron.Realization))
    (fun n => TopCat.ofHom ((commonSuccessorSystem X).polyhedralTransition n))

private def originalToCommon : originalSequence X ⟶ commonSequence X :=
  NatTrans.ofSequence (fun n => TopCat.ofHom (((commonSuccessorSystem X).stages n).original))
    (fun n => by
      simp only [originalSequence, commonSequence, Functor.ofSequence_map_homOfLE_succ]
      change skeletonTransition X (n + 1) ≫
          TopCat.ofHom (((commonSuccessorSystem X).stages (n + 1)).original) =
        TopCat.ofHom (((commonSuccessorSystem X).stages n).original) ≫
          TopCat.ofHom ((commonSuccessorSystem X).transition n)
      apply ConcreteCategory.hom_ext
      intro x
      simpa only [TopCat.comp_app, TopCat.ofHom_apply] using!
        (commonSuccessorSystem X).transition_original n x)

private def polyhedralToCommon : polyhedralSequence X ⟶ commonSequence X :=
  NatTrans.ofSequence (fun n => TopCat.ofHom (((commonSuccessorSystem X).stages n).polyhedral))
    (fun n => by
      simp only [polyhedralSequence, commonSequence, Functor.ofSequence_map_homOfLE_succ]
      change TopCat.ofHom ((commonSuccessorSystem X).polyhedralTransition n) ≫
          TopCat.ofHom (((commonSuccessorSystem X).stages (n + 1)).polyhedral) =
        TopCat.ofHom (((commonSuccessorSystem X).stages n).polyhedral) ≫
          TopCat.ofHom ((commonSuccessorSystem X).transition n)
      apply ConcreteCategory.hom_ext
      intro p
      simpa only [TopCat.comp_app, TopCat.ofHom_apply] using!
        (commonSuccessorSystem X).transition_polyhedral n p)

private theorem commonSequence_map_closed {i j : ℕ} (f : i ⟶ j) :
    IsClosedEmbedding ((commonSequence X).map f).hom := by
  have h (i j : ℕ) (hij : i ≤ j) :
      IsClosedEmbedding ((commonSequence X).map (homOfLE hij)).hom := by
    induction j, hij using Nat.le_induction with
    | base =>
        have hid : (commonSequence X).map (homOfLE (le_refl i)) =
            𝟙 ((commonSequence X).obj i) := (commonSequence X).map_id i
        rw [hid]
        exact Topology.IsClosedEmbedding.id
    | succ j hij ih =>
        have he : homOfLE (hij.trans (Nat.le_succ j)) =
            homOfLE hij ≫ homOfLE (Nat.le_succ j) := rfl
        rw [he, Functor.map_comp]
        have hs : ((commonSequence X).map (homOfLE (Nat.le_succ j))).hom =
            (commonSuccessorSystem X).transition j := by
          simp only [commonSequence, Functor.ofSequence_map_homOfLE_succ]
          rfl
        simpa only [TopCat.hom_comp, ContinuousMap.coe_comp, hs] using!
          ((commonSuccessorSystem X).transition_closed j).comp ih
  simpa only [homOfLE_leOfHom] using! h i j (leOfHom f)

private def commonUnion : TopCat.{u} := colimit (commonSequence X)

private def commonStageInclusion (n : ℕ) :
    ((commonSuccessorSystem X).stages n).space ⟶ commonUnion X :=
  colimit.ι (commonSequence X) n

private theorem commonStageInclusion_successor (n : ℕ) :
    TopCat.ofHom ((commonSuccessorSystem X).transition n) ≫ commonStageInclusion X (n + 1) =
      commonStageInclusion X n := by
  simpa only [commonSequence, commonStageInclusion, Functor.ofSequence_map_homOfLE_succ] using!
    colimit.w (commonSequence X) (homOfLE (n.le_add_right 1))

private theorem commonStageInclusion_closed (n : ℕ) :
    IsClosedEmbedding (commonStageInclusion X n).hom :=
  TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding
    (colimit.cocone (commonSequence X)) (colimit.isColimit (commonSequence X))
    (fun _ _ f => commonSequence_map_closed X f) n

private def commonStageSigmaQuotient :
    TopCat.of (Σ n : ℕ, ((commonSuccessorSystem X).stages n).space) ⟶ commonUnion X :=
  TopCat.ofHom
    { toFun := fun p => commonStageInclusion X p.1 p.2
      continuous_toFun := continuous_sigma fun n => (commonStageInclusion X n).hom.continuous }

private theorem commonStageSigmaQuotient_surjective :
    Function.Surjective (commonStageSigmaQuotient X) := by
  intro z
  let hc := isColimitOfPreserves (forget TopCat) (colimit.isColimit (commonSequence X))
  obtain ⟨n, x, hx⟩ := Types.jointly_surjective_of_isColimit hc z
  exact ⟨⟨n, x⟩, hx⟩

private theorem commonUnion_isClosed_iff (A : Set (commonUnion X)) :
    IsClosed A ↔ ∀ n, IsClosed ((commonStageInclusion X n) ⁻¹' A) :=
  TopCat.isClosed_iff_of_isColimit _ (colimit.isColimit (commonSequence X)) A

private theorem commonUnion_continuous_iff {Y : Type*} [TopologicalSpace Y]
    (f : commonUnion X → Y) :
    Continuous f ↔ ∀ n, Continuous (f ∘ commonStageInclusion X n) :=
  TopCat.continuous_iff_of_isColimit _ (colimit.isColimit (commonSequence X)) f

private theorem isQuotientMap_commonStageSigmaQuotient :
    IsQuotientMap (commonStageSigmaQuotient X) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨commonStageSigmaQuotient_surjective X, ?_⟩
  intro A
  rw [commonUnion_isClosed_iff X A, isClosed_sigma_iff]
  rfl

private def originalCocone : Cocone (originalSequence X) where
  pt := X
  ι := NatTrans.ofSequence (fun n => skeletonInclusion X (n + 1))
    (fun n => by
      simp only [originalSequence, Functor.ofSequence_map_homOfLE_succ]
      exact skeletonTransition_comp_inclusion X (n + 1))

private def originalCocone_typeIsColimit :
    IsColimit ((forget TopCat).mapCocone (originalCocone X)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨⟨⟨m, j⟩, q⟩, rfl⟩ := characteristicQuotient_surjective X x
    exact ⟨m, characteristicDiskToSkeleton m j q, rfl⟩
  · intro i x y hxy
    have hval : x.val = y.val := hxy
    have hpoint : x = y := Subtype.ext hval
    refine ⟨i, 𝟙 i, ?_⟩
    rw [((originalSequence X) ⋙ forget TopCat).map_id i]
    exact hpoint

private theorem originalCocone_isClosed_iff (A : Set X) :
    IsClosed A ↔ ∀ n, IsClosed ((skeletonInclusion X (n + 1)) ⁻¹' A) := by
  constructor
  · intro hA n
    exact hA.preimage (skeletonInclusion X (n + 1)).hom.continuous
  · intro hA
    apply (isQuotientMap_iff_isClosed.mp (isQuotientMap_characteristicQuotient X)).2 A |>.mpr
    rw [isClosed_sigma_iff]
    rintro ⟨m, j⟩
    exact (hA m).preimage (characteristicDiskToSkeleton m j).hom.continuous

private def originalCocone_isColimit : IsColimit (originalCocone X) := by
  apply Classical.choice
  rw [TopCat.nonempty_isColimit_iff_eq_coinduced (originalCocone X)
    (originalCocone_typeIsColimit X)]
  apply TopologicalSpace.ext_isClosed
  intro A
  simp only [isClosed_iSup_iff, isClosed_coinduced]
  exact originalCocone_isClosed_iff X A

private def originalUnionIso : colimit (originalSequence X) ≅ X :=
  (colimit.isColimit (originalSequence X)).coconePointUniqueUpToIso
    (originalCocone_isColimit X)

private theorem originalUnionIso_leg (n : ℕ) :
    colimit.ι (originalSequence X) n ≫ (originalUnionIso X).hom =
      skeletonInclusion X (n + 1) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (originalSequence X)) (originalCocone_isColimit X) n

private def originalUnionToCommon : colimit (originalSequence X) ⟶ commonUnion X :=
  colim.map (originalToCommon X)

private theorem commonSequence_original_preimage {i j : ℕ} (f : i ⟶ j) :
    ((commonSequence X).map f).hom ⁻¹'
        Set.range ((commonSuccessorSystem X).stages j).original =
      Set.range ((commonSuccessorSystem X).stages i).original := by
  have h (i j : ℕ) (hij : i ≤ j) :
      ((commonSequence X).map (homOfLE hij)).hom ⁻¹'
          Set.range ((commonSuccessorSystem X).stages j).original =
        Set.range ((commonSuccessorSystem X).stages i).original := by
    induction j, hij using Nat.le_induction with
    | base =>
        have hid : (commonSequence X).map (homOfLE (le_refl i)) =
            𝟙 ((commonSequence X).obj i) := (commonSequence X).map_id i
        rw [hid]
        rfl
    | succ j hij ih =>
        have he : homOfLE (hij.trans (Nat.le_succ j)) =
            homOfLE hij ≫ homOfLE (Nat.le_succ j) := rfl
        rw [he, Functor.map_comp]
        have hs : ((commonSequence X).map (homOfLE (Nat.le_succ j))).hom =
            (commonSuccessorSystem X).transition j := by
          simp only [commonSequence, Functor.ofSequence_map_homOfLE_succ]
          rfl
        have hcomp :
            (((commonSequence X).map (homOfLE hij) ≫
              (commonSequence X).map (homOfLE (Nat.le_succ j))).hom :
                (commonSequence X).obj i → (commonSequence X).obj (j + 1)) =
            ((commonSuccessorSystem X).transition j :
                ((commonSuccessorSystem X).stages j).space →
                  ((commonSuccessorSystem X).stages (j + 1)).space) ∘
              ((commonSequence X).map (homOfLE hij)).hom := by
          funext x
          exact congrArg (fun g => g (((commonSequence X).map (homOfLE hij)).hom x)) hs
        let g : (commonSequence X).obj i → ((commonSuccessorSystem X).stages j).space :=
          ((commonSequence X).map (homOfLE hij)).hom
        let t : ((commonSuccessorSystem X).stages j).space →
            ((commonSuccessorSystem X).stages (j + 1)).space :=
          (commonSuccessorSystem X).transition j
        let A : Set ((commonSuccessorSystem X).stages (j + 1)).space :=
          Set.range ((commonSuccessorSystem X).stages (j + 1)).original
        have hp : (t ∘ g) ⁻¹' A = g ⁻¹' (t ⁻¹' A) := Set.preimage_comp
        have hpre : t ⁻¹' A = Set.range ((commonSuccessorSystem X).stages j).original :=
          (commonSuccessorSystem X).original_preimage j
        have h₁ :
            (((commonSequence X).map (homOfLE hij) ≫
              (commonSequence X).map (homOfLE (Nat.le_succ j))).hom) ⁻¹' A =
              g ⁻¹' (t ⁻¹' A) :=
          (congrArg (fun q : (commonSequence X).obj i →
              ((commonSuccessorSystem X).stages (j + 1)).space => q ⁻¹' A) hcomp).trans hp
        exact h₁.trans ((congrArg (fun B : Set ((commonSuccessorSystem X).stages j).space =>
          g ⁻¹' B) hpre).trans ih)
  simpa only [homOfLE_leOfHom] using! h i j (leOfHom f)

private theorem originalSequence_map_value {i j : ℕ} (f : i ⟶ j)
    (x : skeletonTop X (i + 1)) :
    skeletonInclusion X (j + 1) ((originalSequence X).map f x) =
      skeletonInclusion X (i + 1) x := by
  have h := (originalCocone X).w f
  exact ConcreteCategory.congr_hom h x

private def originalXToCommon : X ⟶ commonUnion X :=
  (originalUnionIso X).inv ≫ originalUnionToCommon X

private theorem originalXToCommon_stage (n : ℕ) :
    skeletonInclusion X (n + 1) ≫ originalXToCommon X =
      TopCat.ofHom (((commonSuccessorSystem X).stages n).original) ≫
        commonStageInclusion X n := by
  have h₁ : skeletonInclusion X (n + 1) ≫ (originalUnionIso X).inv =
      colimit.ι (originalSequence X) n := by
    have hleg : colimit.ι (originalSequence X) n ≫ (originalUnionIso X).hom =
        (originalCocone X).ι.app n := originalUnionIso_leg X n
    have hcancel :
        (colimit.ι (originalSequence X) n ≫ (originalUnionIso X).hom) ≫
            (originalUnionIso X).inv = colimit.ι (originalSequence X) n := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact Eq.trans (congrArg (fun g : (originalSequence X).obj n ⟶ X =>
      g ≫ (originalUnionIso X).inv) hleg.symm) hcancel
  change skeletonInclusion X (n + 1) ≫
      ((originalUnionIso X).inv ≫ colim.map (originalToCommon X)) = _
  rw [← Category.assoc, h₁]
  simpa only [originalToCommon, commonStageInclusion] using!
    colimit.ι_map (originalToCommon X) n

private abbrev polyhedralUnion : TopCat.{u} := colimit (polyhedralSequence X)

private def polyhedralUnionToCommon : polyhedralUnion X ⟶ commonUnion X :=
  colim.map (polyhedralToCommon X)

private theorem commonStageInclusion_map {i j : ℕ} (f : i ⟶ j)
    (x : (commonSequence X).obj i) :
    commonStageInclusion X j ((commonSequence X).map f x) = commonStageInclusion X i x :=
  ConcreteCategory.congr_hom (colimit.w (commonSequence X) f) x

private theorem originalToCommon_map_value {i j : ℕ} (f : i ⟶ j)
    (x : skeletonTop X (i + 1)) :
    ((commonSequence X).map f)
        (((commonSuccessorSystem X).stages i).original x) =
      ((commonSuccessorSystem X).stages j).original ((originalSequence X).map f x) := by
  have h := ConcreteCategory.congr_hom ((originalToCommon X).naturality f) x
  exact h.symm

private theorem commonStageInclusion_eq_at_max (i j : ℕ)
    (x : (commonSequence X).obj i) (y : (commonSequence X).obj j)
    (hxy : commonStageInclusion X i x = commonStageInclusion X j y) :
    (commonSequence X).map (homOfLE (Nat.le_max_left i j)) x =
      (commonSequence X).map (homOfLE (Nat.le_max_right i j)) y := by
  apply (commonStageInclusion_closed X (max i j)).injective
  exact (commonStageInclusion_map X (homOfLE (Nat.le_max_left i j)) x).trans
    (hxy.trans (commonStageInclusion_map X (homOfLE (Nat.le_max_right i j)) y).symm)

private theorem originalXToCommon_injective : Function.Injective (originalXToCommon X) := by
  intro x y hxy
  obtain ⟨n, a, ha⟩ := Types.jointly_surjective_of_isColimit (originalCocone_typeIsColimit X) x
  obtain ⟨m, b, hb⟩ := Types.jointly_surjective_of_isColimit (originalCocone_typeIsColimit X) y
  have hxa : originalXToCommon X (skeletonInclusion X (n + 1) a) =
      commonStageInclusion X n (((commonSuccessorSystem X).stages n).original a) :=
    ConcreteCategory.congr_hom (originalXToCommon_stage X n) a
  have hyb : originalXToCommon X (skeletonInclusion X (m + 1) b) =
      commonStageInclusion X m (((commonSuccessorSystem X).stages m).original b) :=
    ConcreteCategory.congr_hom (originalXToCommon_stage X m) b
  have hstage : commonStageInclusion X n (((commonSuccessorSystem X).stages n).original a) =
      commonStageInclusion X m (((commonSuccessorSystem X).stages m).original b) :=
    hxa.symm.trans ((congrArg (originalXToCommon X) ha).trans
      (hxy.trans ((congrArg (originalXToCommon X) hb).symm.trans hyb)))
  let f : n ⟶ max n m := homOfLE (Nat.le_max_left n m)
  let g : m ⟶ max n m := homOfLE (Nat.le_max_right n m)
  have hcommon := commonStageInclusion_eq_at_max X n m
    (((commonSuccessorSystem X).stages n).original a)
    (((commonSuccessorSystem X).stages m).original b) hstage
  have horig : ((originalSequence X).map f) a = ((originalSequence X).map g) b := by
    apply (((commonSuccessorSystem X).stages (max n m)).original_closed).injective
    exact (originalToCommon_map_value X f a).symm.trans
      (hcommon.trans (originalToCommon_map_value X g b))
  have hval := congrArg (fun z : skeletonTop X (max n m + 1) =>
    skeletonInclusion X (max n m + 1) z) horig
  exact ha.symm.trans ((originalSequence_map_value X f a).symm.trans
    (hval.trans ((originalSequence_map_value X g b).trans hb)))

private theorem originalXToCommon_image_stage (n : ℕ) (A : Set X) :
    (commonStageInclusion X n) ⁻¹' ((originalXToCommon X) '' A) =
      ((commonSuccessorSystem X).stages n).original ''
        ((skeletonInclusion X (n + 1)) ⁻¹' A) := by
  ext x
  constructor
  · rintro ⟨y, hyA, hy⟩
    obtain ⟨m, b, hb⟩ := Types.jointly_surjective_of_isColimit
      (originalCocone_typeIsColimit X) y
    have hstage : commonStageInclusion X n x =
        commonStageInclusion X m (((commonSuccessorSystem X).stages m).original b) :=
      hy.symm.trans ((congrArg (originalXToCommon X) hb).symm.trans
        (ConcreteCategory.congr_hom (originalXToCommon_stage X m) b))
    let f : n ⟶ max n m := homOfLE (Nat.le_max_left n m)
    let g : m ⟶ max n m := homOfLE (Nat.le_max_right n m)
    have hcommon := commonStageInclusion_eq_at_max X n m x
      (((commonSuccessorSystem X).stages m).original b) hstage
    have hm : (commonSequence X).map f x ∈
        Set.range ((commonSuccessorSystem X).stages (max n m)).original := by
      refine ⟨(originalSequence X).map g b, ?_⟩
      exact (originalToCommon_map_value X g b).symm.trans hcommon.symm
    have hx : x ∈ Set.range ((commonSuccessorSystem X).stages n).original :=
      (Set.ext_iff.mp (commonSequence_original_preimage X f) x).mp hm
    obtain ⟨a, ha⟩ := hx
    have hglobal : originalXToCommon X (skeletonInclusion X (n + 1) a) =
        originalXToCommon X y :=
      (ConcreteCategory.congr_hom (originalXToCommon_stage X n) a).trans
        ((congrArg (commonStageInclusion X n) ha).trans hy.symm)
    have hay : skeletonInclusion X (n + 1) a = y := originalXToCommon_injective X hglobal
    have haA : skeletonInclusion X (n + 1) a ∈ A :=
      Eq.mpr (congrArg (fun z : X => z ∈ A) hay) hyA
    exact ⟨a, haA, ha⟩
  · rintro ⟨a, haA, rfl⟩
    exact ⟨skeletonInclusion X (n + 1) a, haA,
      ConcreteCategory.congr_hom (originalXToCommon_stage X n) a⟩

private theorem originalXToCommon_isClosedMap : IsClosedMap (originalXToCommon X) := by
  intro A hA
  apply (commonUnion_isClosed_iff X ((originalXToCommon X) '' A)).mpr
  intro n
  rw [originalXToCommon_image_stage]
  exact (((commonSuccessorSystem X).stages n).original_closed).isClosedMap _
    (hA.preimage (skeletonInclusion X (n + 1)).hom.continuous)

private theorem originalXToCommon_isClosedEmbedding : IsClosedEmbedding (originalXToCommon X) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (originalXToCommon X).hom.continuous (originalXToCommon_injective X)
    (originalXToCommon_isClosedMap X)
private theorem commonSequence_polyhedral_preimage {i j : ℕ} (f : i ⟶ j) :
    ((commonSequence X).map f).hom ⁻¹'
        Set.range ((commonSuccessorSystem X).stages j).polyhedral =
      Set.range ((commonSuccessorSystem X).stages i).polyhedral := by
  have h (i j : ℕ) (hij : i ≤ j) :
      ((commonSequence X).map (homOfLE hij)).hom ⁻¹'
          Set.range ((commonSuccessorSystem X).stages j).polyhedral =
        Set.range ((commonSuccessorSystem X).stages i).polyhedral := by
    induction j, hij using Nat.le_induction with
    | base =>
        have hid : (commonSequence X).map (homOfLE (le_refl i)) =
            𝟙 ((commonSequence X).obj i) := (commonSequence X).map_id i
        rw [hid]
        rfl
    | succ j hij ih =>
        have he : homOfLE (hij.trans (Nat.le_succ j)) =
            homOfLE hij ≫ homOfLE (Nat.le_succ j) := rfl
        rw [he, Functor.map_comp]
        have hs : ((commonSequence X).map (homOfLE (Nat.le_succ j))).hom =
            (commonSuccessorSystem X).transition j := by
          simp only [commonSequence, Functor.ofSequence_map_homOfLE_succ]
          rfl
        have hcomp :
            (((commonSequence X).map (homOfLE hij) ≫
              (commonSequence X).map (homOfLE (Nat.le_succ j))).hom :
                (commonSequence X).obj i → (commonSequence X).obj (j + 1)) =
            ((commonSuccessorSystem X).transition j :
                ((commonSuccessorSystem X).stages j).space →
                  ((commonSuccessorSystem X).stages (j + 1)).space) ∘
              ((commonSequence X).map (homOfLE hij)).hom := by
          funext x
          exact congrArg (fun g => g (((commonSequence X).map (homOfLE hij)).hom x)) hs
        let g : (commonSequence X).obj i → ((commonSuccessorSystem X).stages j).space :=
          ((commonSequence X).map (homOfLE hij)).hom
        let t : ((commonSuccessorSystem X).stages j).space →
            ((commonSuccessorSystem X).stages (j + 1)).space :=
          (commonSuccessorSystem X).transition j
        let A : Set ((commonSuccessorSystem X).stages (j + 1)).space :=
          Set.range ((commonSuccessorSystem X).stages (j + 1)).polyhedral
        have hp : (t ∘ g) ⁻¹' A = g ⁻¹' (t ⁻¹' A) := Set.preimage_comp
        have hpre : t ⁻¹' A = Set.range ((commonSuccessorSystem X).stages j).polyhedral :=
          (commonSuccessorSystem X).polyhedral_preimage j
        have h₁ :
            (((commonSequence X).map (homOfLE hij) ≫
              (commonSequence X).map (homOfLE (Nat.le_succ j))).hom) ⁻¹' A =
              g ⁻¹' (t ⁻¹' A) :=
          (congrArg (fun q : (commonSequence X).obj i →
              ((commonSuccessorSystem X).stages (j + 1)).space => q ⁻¹' A) hcomp).trans hp
        exact h₁.trans ((congrArg (fun B : Set ((commonSuccessorSystem X).stages j).space =>
          g ⁻¹' B) hpre).trans ih)
  simpa only [homOfLE_leOfHom] using! h i j (leOfHom f)


private theorem polyhedralUnionToCommon_stage (n : ℕ) :
    colimit.ι (polyhedralSequence X) n ≫ polyhedralUnionToCommon X =
      TopCat.ofHom (((commonSuccessorSystem X).stages n).polyhedral) ≫
        commonStageInclusion X n := by
  simpa only [polyhedralUnionToCommon, polyhedralToCommon, commonStageInclusion] using!
    colimit.ι_map (polyhedralToCommon X) n

private theorem polyhedralStage_map_value {i j : ℕ} (f : i ⟶ j)
    (x : (polyhedralSequence X).obj i) :
    ((commonSequence X).map f) (((commonSuccessorSystem X).stages i).polyhedral x) =
      ((commonSuccessorSystem X).stages j).polyhedral ((polyhedralSequence X).map f x) :=
  (ConcreteCategory.congr_hom ((polyhedralToCommon X).naturality f) x).symm

private theorem polyhedralUnionToCommon_injective :
    Function.Injective (polyhedralUnionToCommon X) := by
  intro x y hxy
  have hc := isColimitOfPreserves (forget TopCat) (colimit.isColimit (polyhedralSequence X))
  obtain ⟨n, a, ha⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨m, b, hb⟩ := Types.jointly_surjective_of_isColimit hc y
  have hxa := ConcreteCategory.congr_hom (polyhedralUnionToCommon_stage X n) a
  have hyb := ConcreteCategory.congr_hom (polyhedralUnionToCommon_stage X m) b
  have hstage : commonStageInclusion X n (((commonSuccessorSystem X).stages n).polyhedral a) =
      commonStageInclusion X m (((commonSuccessorSystem X).stages m).polyhedral b) :=
    hxa.symm.trans ((congrArg (polyhedralUnionToCommon X) ha).trans
      (hxy.trans ((congrArg (polyhedralUnionToCommon X) hb).symm.trans hyb)))
  let f : n ⟶ max n m := homOfLE (Nat.le_max_left n m)
  let g : m ⟶ max n m := homOfLE (Nat.le_max_right n m)
  have hcommon := commonStageInclusion_eq_at_max X n m
    (((commonSuccessorSystem X).stages n).polyhedral a)
    (((commonSuccessorSystem X).stages m).polyhedral b) hstage
  have hpoly : (polyhedralSequence X).map f a = (polyhedralSequence X).map g b := by
    apply (((commonSuccessorSystem X).stages (max n m)).polyhedral_closed).injective
    exact (polyhedralStage_map_value X f a).symm.trans
      (hcommon.trans (polyhedralStage_map_value X g b))
  have hfa := ConcreteCategory.congr_hom (colimit.w (polyhedralSequence X) f) a
  have hgb := ConcreteCategory.congr_hom (colimit.w (polyhedralSequence X) g) b
  exact ha.symm.trans (hfa.symm.trans
    ((congrArg (fun z : (polyhedralSequence X).obj (max n m) =>
      colimit.ι (polyhedralSequence X) (max n m) z) hpoly).trans (hgb.trans hb)))

private theorem polyhedralUnionToCommon_image_stage (n : ℕ)
    (A : Set (polyhedralUnion X)) :
    (commonStageInclusion X n) ⁻¹' ((polyhedralUnionToCommon X) '' A) =
      ((commonSuccessorSystem X).stages n).polyhedral ''
        ((colimit.ι (polyhedralSequence X) n) ⁻¹' A) := by
  ext x
  constructor
  · rintro ⟨y, hyA, hy⟩
    have hc := isColimitOfPreserves (forget TopCat) (colimit.isColimit (polyhedralSequence X))
    obtain ⟨m, b, hb⟩ := Types.jointly_surjective_of_isColimit hc y
    have hstage : commonStageInclusion X n x =
        commonStageInclusion X m (((commonSuccessorSystem X).stages m).polyhedral b) :=
      hy.symm.trans ((congrArg (polyhedralUnionToCommon X) hb).symm.trans
        (ConcreteCategory.congr_hom (polyhedralUnionToCommon_stage X m) b))
    let f : n ⟶ max n m := homOfLE (Nat.le_max_left n m)
    let g : m ⟶ max n m := homOfLE (Nat.le_max_right n m)
    have hcommon := commonStageInclusion_eq_at_max X n m x
      (((commonSuccessorSystem X).stages m).polyhedral b) hstage
    have hm : (commonSequence X).map f x ∈
        Set.range ((commonSuccessorSystem X).stages (max n m)).polyhedral :=
      ⟨(polyhedralSequence X).map g b,
        (polyhedralStage_map_value X g b).symm.trans hcommon.symm⟩
    have hx : x ∈ Set.range ((commonSuccessorSystem X).stages n).polyhedral :=
      (Set.ext_iff.mp (commonSequence_polyhedral_preimage X f) x).mp hm
    obtain ⟨a, ha⟩ := hx
    have hglobal : polyhedralUnionToCommon X (colimit.ι (polyhedralSequence X) n a) =
        polyhedralUnionToCommon X y :=
      (ConcreteCategory.congr_hom (polyhedralUnionToCommon_stage X n) a).trans
        ((congrArg (commonStageInclusion X n) ha).trans hy.symm)
    have hay := polyhedralUnionToCommon_injective X hglobal
    have haA : colimit.ι (polyhedralSequence X) n a ∈ A :=
      Eq.mpr (congrArg (fun z : polyhedralUnion X => z ∈ A) hay) hyA
    exact ⟨a, haA, ha⟩
  · rintro ⟨a, haA, rfl⟩
    exact ⟨colimit.ι (polyhedralSequence X) n a, haA,
      ConcreteCategory.congr_hom (polyhedralUnionToCommon_stage X n) a⟩

private theorem polyhedralUnionToCommon_isClosedMap : IsClosedMap (polyhedralUnionToCommon X) := by
  intro A hA
  apply (commonUnion_isClosed_iff X ((polyhedralUnionToCommon X) '' A)).mpr
  intro n
  rw [polyhedralUnionToCommon_image_stage]
  exact (((commonSuccessorSystem X).stages n).polyhedral_closed).isClosedMap _
    (hA.preimage (colimit.ι (polyhedralSequence X) n).hom.continuous)

private theorem polyhedralUnionToCommon_isClosedEmbedding :
    IsClosedEmbedding (polyhedralUnionToCommon X) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (polyhedralUnionToCommon X).hom.continuous (polyhedralUnionToCommon_injective X)
    (polyhedralUnionToCommon_isClosedMap X)

private theorem originalXToCommon_range_stage (n : ℕ) :
    (commonStageInclusion X n) ⁻¹' Set.range (originalXToCommon X) =
      Set.range ((commonSuccessorSystem X).stages n).original := by
  simpa only [Set.image_univ, Set.preimage_univ] using!
    originalXToCommon_image_stage X n Set.univ

private theorem polyhedralUnionToCommon_range_stage (n : ℕ) :
    (commonStageInclusion X n) ⁻¹' Set.range (polyhedralUnionToCommon X) =
      Set.range ((commonSuccessorSystem X).stages n).polyhedral := by
  have h := polyhedralUnionToCommon_image_stage X n Set.univ
  have hA : (colimit.ι (polyhedralSequence X) n) ⁻¹'
      (Set.univ : Set (polyhedralUnion X)) =
      (Set.univ : Set ((polyhedralSequence X).obj n)) := Set.preimage_univ
  have hL : (polyhedralUnionToCommon X) '' (Set.univ : Set (polyhedralUnion X)) =
      Set.range (polyhedralUnionToCommon X) := Set.image_univ
  have hR : ((commonSuccessorSystem X).stages n).polyhedral ''
      (Set.univ : Set ((polyhedralSequence X).obj n)) =
      Set.range ((commonSuccessorSystem X).stages n).polyhedral := Set.image_univ
  exact (congrArg (fun A : Set (commonUnion X) => (commonStageInclusion X n) ⁻¹' A)
    hL).symm.trans (h.trans
      ((congrArg (fun A : Set ((polyhedralSequence X).obj n) =>
        ((commonSuccessorSystem X).stages n).polyhedral '' A) hA).trans hR))

private theorem commonStageInclusion_initial (n : ℕ) :
    TopCat.ofHom ((commonSuccessorSystem X).initialToStage n) ≫
      commonStageInclusion X n = commonStageInclusion X 0 := by
  induction n with
  | zero =>
      rw [(commonSuccessorSystem X).initialToStage_zero]
      rfl
  | succ n ih =>
      have hstep := ConcreteCategory.congr_hom (commonStageInclusion_successor X n)
      apply TopCat.ext
      intro x
      have hpoint :
          commonStageInclusion X (n + 1) ((commonSuccessorSystem X).initialToStage (n + 1) x) =
            commonStageInclusion X n ((commonSuccessorSystem X).initialToStage n x) := by
        rw [(commonSuccessorSystem X).initialToStage_succ]
        exact hstep ((commonSuccessorSystem X).initialToStage n x)
      exact hpoint.trans (ConcreteCategory.congr_hom ih x)

private theorem commonUnion_end_intersection :
    Set.range (originalXToCommon X) ∩ Set.range (polyhedralUnionToCommon X) =
      Set.range (commonStageInclusion X 0) := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨n, x⟩, hx⟩ := commonStageSigmaQuotient_surjective X z
    have ho : x ∈ Set.range ((commonSuccessorSystem X).stages n).original :=
      (Set.ext_iff.mp (originalXToCommon_range_stage X n) x).mp
        (Eq.mpr (congrArg (fun y : commonUnion X => y ∈ Set.range (originalXToCommon X)) hx) hz.1)
    have hp : x ∈ Set.range ((commonSuccessorSystem X).stages n).polyhedral :=
      (Set.ext_iff.mp (polyhedralUnionToCommon_range_stage X n) x).mp
        (Eq.mpr (congrArg (fun y : commonUnion X => y ∈ Set.range (polyhedralUnionToCommon X)) hx) hz.2)
    have hi : x ∈ Set.range ((commonSuccessorSystem X).initialToStage n) :=
      (Set.ext_iff.mp ((commonSuccessorSystem X).zero_intersection n) x).mp ⟨ho, hp⟩
    obtain ⟨a, ha⟩ := hi
    refine ⟨a, ?_⟩
    exact (ConcreteCategory.congr_hom (commonStageInclusion_initial X n) a).symm.trans
      ((congrArg (commonStageInclusion X n) ha).trans hx)
  · rintro ⟨a, rfl⟩
    have hzero : a ∈ Set.range ((commonSuccessorSystem X).initialToStage 0) := by
      refine ⟨a, ?_⟩
      rw [(commonSuccessorSystem X).initialToStage_zero]
      rfl
    have hb : a ∈ Set.range ((commonSuccessorSystem X).stages 0).original ∩
        Set.range ((commonSuccessorSystem X).stages 0).polyhedral :=
      (Set.ext_iff.mp ((commonSuccessorSystem X).zero_intersection 0) a).mpr hzero
    exact ⟨(Set.ext_iff.mp (originalXToCommon_range_stage X 0) a).mpr hb.1,
      (Set.ext_iff.mp (polyhedralUnionToCommon_range_stage X 0) a).mpr hb.2⟩

end ActualCommonDimensionUnionConstruction

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex PreAbstractSimplicialComplex
open scoped Classical

universe u

namespace ActualPolyhedralDimensionUnionConstruction

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

private def vertexSequence : ℕ ⥤ Type u :=
  Functor.ofSequence
    (X := fun n => ((commonSuccessorSystem X).stages n).vertices)
    (fun n => TypeCat.ofHom (commonSuccessorSystemVertexTransition X n))

private theorem vertexSequence_map_injective {i j : ℕ} (f : i ⟶ j) :
    Function.Injective ((vertexSequence X).map f) := by
  have h (i j : ℕ) (hij : i ≤ j) :
      Function.Injective ((vertexSequence X).map (homOfLE hij)) := by
    induction j, hij using Nat.le_induction with
    | base =>
        have hid : (vertexSequence X).map (homOfLE (le_refl i)) =
            𝟙 ((vertexSequence X).obj i) := (vertexSequence X).map_id i
        rw [hid]
        intro x y hxy
        simpa only [ConcreteCategory.id_apply] using! hxy
    | succ j hij ih =>
        have he : homOfLE (hij.trans (Nat.le_succ j)) =
            homOfLE hij ≫ homOfLE (Nat.le_succ j) := rfl
        rw [he, (vertexSequence X).map_comp]
        have hs : (vertexSequence X).map (homOfLE (Nat.le_succ j)) =
            TypeCat.ofHom (commonSuccessorSystemVertexTransition X j) := by
          simp only [vertexSequence, Functor.ofSequence_map_homOfLE_succ]
          rfl
        rw [hs]
        intro x y hxy
        apply ih
        apply (commonSuccessorSystemVertexTransition X j).injective
        simpa only [ConcreteCategory.comp_apply, TypeCat.ofHom,
          ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk] using! hxy
  simpa only [homOfLE_leOfHom] using! h i j (leOfHom f)

private abbrev unionVertices : Type u := colimit (vertexSequence X)

private def stageVertexEmbedding (n : ℕ) :
    ((commonSuccessorSystem X).stages n).vertices ↪ unionVertices X where
  toFun := colimit.ι (vertexSequence X) n
  inj' := by
    intro x y hxy
    obtain ⟨k, f, hfk⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff'
        (colimit.isColimit (vertexSequence X)) x y).mp hxy
    exact vertexSequence_map_injective X f hfk

private theorem stageVertexEmbedding_successor (n : ℕ) :
    (commonSuccessorSystemVertexTransition X n).trans (stageVertexEmbedding X (n + 1)) =
      stageVertexEmbedding X n := by
  apply Function.Embedding.ext
  intro v
  have hw := ConcreteCategory.congr_hom
    (colimit.w (vertexSequence X) (homOfLE (n.le_add_right 1))) v
  simpa only [vertexSequence, stageVertexEmbedding,
    Functor.ofSequence_map_homOfLE_succ, ConcreteCategory.comp_apply,
    TypeCat.ofHom, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk] using! hw

private def mappedStageComplex (n : ℕ) : PreAbstractSimplicialComplex (unionVertices X) :=
  MappingCylinder.relabelComplex ((commonSuccessorSystem X).stages n).polyhedron
    (stageVertexEmbedding X n)

private def unionComplex : PreAbstractSimplicialComplex (unionVertices X) where
  faces := {s | ∃ n : ℕ, s ∈ mappedStageComplex X n}
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨n, hn⟩ := hs
    refine ⟨((mappedStageComplex X n).isRelLowerSet_faces hn).1, ?_⟩
    intro t hts ht
    exact ⟨n, ((mappedStageComplex X n).isRelLowerSet_faces hn).2 hts ht⟩

private theorem unionComplex_faces (s : Finset (unionVertices X)) :
    s ∈ unionComplex X ↔ ∃ n : ℕ, s ∈ mappedStageComplex X n := Iff.rfl

private theorem unionComplex_exact_stage_images (s : Finset (unionVertices X)) :
    s ∈ unionComplex X ↔ ∃ (n : ℕ)
      (a : Finset ((commonSuccessorSystem X).stages n).vertices),
      a ∈ ((commonSuccessorSystem X).stages n).polyhedron ∧
        a.map (stageVertexEmbedding X n) = s := by
  classical
  change (∃ n : ℕ, s ∈ mappedStageComplex X n) ↔ _
  constructor
  · rintro ⟨n, a, ha, has⟩
    refine ⟨n, a, ha, ?_⟩
    rw [← has]
    ext v
    simp only [Finset.mem_map, Finset.mem_image]
  · rintro ⟨n, a, ha, has⟩
    refine ⟨n, a, ha, ?_⟩
    rw [← has]
    ext v
    simp only [Finset.mem_image, Finset.mem_map]

private theorem mappedStageComplex_le_union (n : ℕ) :
    mappedStageComplex X n ≤ unionComplex X := fun _ hs => ⟨n, hs⟩

private def stageRelabelHomeomorph (n : ℕ) :
    ((commonSuccessorSystem X).stages n).polyhedron.Realization ≃ₜ
      (mappedStageComplex X n).Realization := by
  change ((commonSuccessorSystem X).stages n).polyhedron.Realization ≃ₜ
    (MappingCylinder.relabelComplex ((commonSuccessorSystem X).stages n).polyhedron
      (stageVertexEmbedding X n)).Realization
  exact MappingCylinder.relabelHomeomorph ((commonSuccessorSystem X).stages n).polyhedron
    (stageVertexEmbedding X n)

private def stagePolyhedralInclusion (n : ℕ) :
    C(((commonSuccessorSystem X).stages n).polyhedron.Realization,
      (unionComplex X).Realization) where
  toFun p := Realization.inclusion (mappedStageComplex_le_union X n)
    (stageRelabelHomeomorph X n p)
  continuous_toFun := (Realization.continuous_inclusion (mappedStageComplex_le_union X n)).comp
    (stageRelabelHomeomorph X n).continuous

private theorem stagePolyhedralInclusion_point (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    (stagePolyhedralInclusion X n p).point = p.point.map (stageVertexEmbedding X n) := by
  simpa only [stagePolyhedralInclusion, stageRelabelHomeomorph, mappedStageComplex,
    Realization.inclusion_point, ← Homeomorph.coe_toEquiv,
    MappingCylinder.relabelHomeomorph, Equiv.coe_ofBijective,
    Equiv.ofBijective_apply] using!
      MappingCylinder.relabelMorphism_point ((commonSuccessorSystem X).stages n).polyhedron
        (stageVertexEmbedding X n) p

private theorem stagePolyhedralInclusion_closed (n : ℕ) :
    IsClosedEmbedding (stagePolyhedralInclusion X n) :=
  (Realization.isClosedEmbedding_inclusion (mappedStageComplex_le_union X n)).comp
    (stageRelabelHomeomorph X n).isClosedEmbedding

private theorem stagePolyhedralInclusion_successor (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    stagePolyhedralInclusion X (n + 1) ((commonSuccessorSystem X).polyhedralTransition n p) =
      stagePolyhedralInclusion X n p := by
  apply Realization.ext
  have hnext := stagePolyhedralInclusion_point X (n + 1)
    ((commonSuccessorSystem X).polyhedralTransition n p)
  have htransport := congrArg (fun q : Convexity.StdSimplex ℝ
      ((commonSuccessorSystem X).stages (n + 1)).vertices =>
        q.map (stageVertexEmbedding X (n + 1)))
    (commonSuccessorSystem_polyhedralTransition_point X n p)
  have hcomp : (p.point.map (commonSuccessorSystemVertexTransition X n)).map
      (stageVertexEmbedding X (n + 1)) = p.point.map (stageVertexEmbedding X n) := by
    rw [Convexity.StdSimplex.map_map]
    change p.point.map ((commonSuccessorSystemVertexTransition X n).trans
      (stageVertexEmbedding X (n + 1))) = p.point.map (stageVertexEmbedding X n)
    rw [stageVertexEmbedding_successor X n]
  exact Eq.trans hnext (Eq.trans htransport
    (Eq.trans hcomp (stagePolyhedralInclusion_point X n p).symm))


/-- A global finite face belongs to one actual relabeled stage, so its chart lifts
through that stage's actual relabeling homeomorphism. -/
private def unionFaceLift (n : ℕ) (t : Face (unionComplex X))
    (ht : t.val ∈ mappedStageComplex X n) :
    C(Convexity.StdSimplex ℝ t.val, ((commonSuccessorSystem X).stages n).polyhedron.Realization) where
  toFun q := (stageRelabelHomeomorph X n).symm
    (Realization.faceMap (mappedStageComplex X n) ⟨t.val, ht⟩ q)
  continuous_toFun := (stageRelabelHomeomorph X n).symm.continuous.comp
    (Realization.continuous_faceMap (mappedStageComplex X n) ⟨t.val, ht⟩)

private theorem unionFaceLift_inclusion (n : ℕ) (t : Face (unionComplex X))
    (ht : t.val ∈ mappedStageComplex X n) (q : Convexity.StdSimplex ℝ t.val) :
    stagePolyhedralInclusion X n (unionFaceLift X n t ht q) =
      Realization.faceMap (unionComplex X) t q := by
  apply Realization.ext
  change ((stageRelabelHomeomorph X n)
    ((stageRelabelHomeomorph X n).symm
      (Realization.faceMap (mappedStageComplex X n) ⟨t.val, ht⟩ q))).point = _
  rw [(stageRelabelHomeomorph X n).apply_symm_apply]
  rfl

/-- The literal weak union topology is exactly the final topology of all the
actual stage images. Every finite face is lifted to one stage; no global
finite-carrier or comparison witness is an input. -/
private theorem unionComplex_continuous_iff {Y : Type*} [TopologicalSpace Y]
    (f : (unionComplex X).Realization → Y) :
    Continuous f ↔ ∀ n, Continuous (f ∘ stagePolyhedralInclusion X n) := by
  constructor
  · intro hf n
    exact hf.comp (stagePolyhedralInclusion X n).continuous
  · intro hf
    apply (Realization.continuous_iff f).mpr
    intro t
    obtain ⟨n, ht⟩ := t.property
    have heq : f ∘ Realization.faceMap (unionComplex X) t =
        (f ∘ stagePolyhedralInclusion X n) ∘ unionFaceLift X n t ht := by
      funext q
      exact congrArg f (unionFaceLift_inclusion X n t ht q).symm
    rw [heq]
    exact (hf n).comp (unionFaceLift X n t ht).continuous

private theorem unionComplex_isClosed_iff (A : Set (unionComplex X).Realization) :
    IsClosed A ↔ ∀ n, IsClosed ((stagePolyhedralInclusion X n) ⁻¹' A) := by
  constructor
  · intro hA n
    exact hA.preimage (stagePolyhedralInclusion X n).continuous
  · intro hA
    apply (Realization.isClosed_iff A).mpr
    intro t
    obtain ⟨n, ht⟩ := t.property
    have heq : (Realization.faceMap (unionComplex X) t) ⁻¹' A =
        (unionFaceLift X n t ht) ⁻¹' ((stagePolyhedralInclusion X n) ⁻¹' A) := by
      ext q
      change Realization.faceMap (unionComplex X) t q ∈ A ↔
        stagePolyhedralInclusion X n (unionFaceLift X n t ht q) ∈ A
      rw [unionFaceLift_inclusion X n t ht q]
    rw [heq]
    exact (hA n).preimage (unionFaceLift X n t ht).continuous


/-- The original public polyhedral transition maps form the actual sequence. -/
private def polyhedralSequence : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence
    (X := fun n => TopCat.of ((commonSuccessorSystem X).stages n).polyhedron.Realization)
    (fun n => TopCat.ofHom ((commonSuccessorSystem X).polyhedralTransition n))

/-- The actual ordinary polyhedral colimit, with its TopCat carrier fixed explicitly. -/
private abbrev polyhedralUnion : TopCat.{u} := colimit (polyhedralSequence X)

private theorem polyhedralSequence_map_succ (n : ℕ) :
    (polyhedralSequence X).map (homOfLE (Nat.le_succ n)) =
      TopCat.ofHom ((commonSuccessorSystem X).polyhedralTransition n) := by
  simp only [polyhedralSequence, Functor.ofSequence_map_homOfLE_succ]
  rfl

/-- Every ordinary sequence arrow is compatible with the same actual vertex-image map. -/
private theorem stagePolyhedralInclusion_map {i j : ℕ} (f : i ⟶ j)
    (p : ((commonSuccessorSystem X).stages i).polyhedron.Realization) :
    stagePolyhedralInclusion X j ((polyhedralSequence X).map f p) =
      stagePolyhedralInclusion X i p := by
  have h (i j : ℕ) (hij : i ≤ j)
      (p : ((commonSuccessorSystem X).stages i).polyhedron.Realization) :
      stagePolyhedralInclusion X j
          ((polyhedralSequence X).map (homOfLE hij) p) =
        stagePolyhedralInclusion X i p := by
    induction j, hij using Nat.le_induction with
    | base =>
        have hid : (polyhedralSequence X).map (homOfLE (le_refl i)) =
            𝟙 ((polyhedralSequence X).obj i) := (polyhedralSequence X).map_id i
        rw [hid]
        rfl
    | succ j hij ih =>
        have he : homOfLE (hij.trans (Nat.le_succ j)) =
            homOfLE hij ≫ homOfLE (Nat.le_succ j) := rfl
        rw [he, (polyhedralSequence X).map_comp, polyhedralSequence_map_succ]
        change stagePolyhedralInclusion X (j + 1)
            ((commonSuccessorSystem X).polyhedralTransition j
              ((polyhedralSequence X).map (homOfLE hij) p)) = _
        exact (stagePolyhedralInclusion_successor X j _).trans ih
  simpa only [homOfLE_leOfHom] using! h i j (leOfHom f) p

private def polyhedralUnionCocone : Cocone (polyhedralSequence X) where
  pt := TopCat.of (unionComplex X).Realization
  ι :=
    { app n := TopCat.ofHom (stagePolyhedralInclusion X n)
      naturality i j f := by
        apply ConcreteCategory.hom_ext
        intro p
        exact stagePolyhedralInclusion_map X f p }

/-- A whole point lifts through its actual finite support face to one original stage. -/
private theorem unionPoint_stageLift (x : (unionComplex X).Realization) :
    ∃ (n : ℕ) (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization),
      stagePolyhedralInclusion X n p = x := by
  obtain ⟨n, hn⟩ := x.support_mem
  let y : (mappedStageComplex X n).Realization := ⟨x.point, hn⟩
  refine ⟨n, (stageRelabelHomeomorph X n).symm y, ?_⟩
  apply Realization.ext
  change ((stageRelabelHomeomorph X n)
    ((stageRelabelHomeomorph X n).symm y)).point = x.point
  rw [(stageRelabelHomeomorph X n).apply_symm_apply]

/-- Recognition uses only the derived point coverage and actual stage injectivity. -/
private def polyhedralUnionType_isColimit :
    IsColimit ((forget TopCat).mapCocone (polyhedralUnionCocone X)) := by
  refine Types.FilteredColimit.isColimitOf'
    (polyhedralSequence X ⋙ forget TopCat)
    ((forget TopCat).mapCocone (polyhedralUnionCocone X)) ?_ ?_
  · intro x
    obtain ⟨n, p, hp⟩ := unionPoint_stageLift X x
    exact ⟨n, p, hp.symm⟩
  · intro n x y hxy
    have hp : stagePolyhedralInclusion X n x = stagePolyhedralInclusion X n y := hxy
    have heq : x = y := (stagePolyhedralInclusion_closed X n).injective hp
    refine ⟨n, 𝟙 n, ?_⟩
    have hid : (polyhedralSequence X ⋙ forget TopCat).map (𝟙 n) =
        𝟙 ((polyhedralSequence X ⋙ forget TopCat).obj n) :=
      (polyhedralSequence X ⋙ forget TopCat).map_id n
    rw [hid]
    simpa only [ConcreteCategory.id_apply] using! heq

/-- The actual weak finite-face topology makes the Type-colimit desc map continuous. -/
private def polyhedralUnion_isColimit : IsColimit (polyhedralUnionCocone X) := by
  let ht := polyhedralUnionType_isColimit X
  refine IsColimit.ofFaithful (forget TopCat) ht
    (fun s => by
      let desc : (unionComplex X).Realization → s.pt :=
        fun x => ht.desc ((forget TopCat).mapCocone s) x
      exact TopCat.ofHom
        { toFun := desc
          continuous_toFun := by
            apply (unionComplex_continuous_iff X desc).mpr
            intro n
            have hcontinuous : Continuous
                (fun p : ((commonSuccessorSystem X).stages n).polyhedron.Realization =>
                  desc (stagePolyhedralInclusion X n p)) := by
              apply (s.ι.app n).hom.continuous.congr
              intro p
              have h := ConcreteCategory.congr_hom
                (ht.fac ((forget TopCat).mapCocone s) n) p
              exact h.symm
            exact hcontinuous })
    (fun s => rfl)

/-- The original ordinary TopCat colimit is homeomorphic to the literal vertex-image complex. -/
private def polyhedralColimitHomeomorph :
    polyhedralUnion X ≃ₜ (unionComplex X).Realization :=
  TopCat.homeoOfIso
    (IsColimit.coconePointUniqueUpToIso
      (colimit.isColimit (polyhedralSequence X)) (polyhedralUnion_isColimit X))

private theorem polyhedralColimitHomeomorph_leg (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    polyhedralColimitHomeomorph X (colimit.ι (polyhedralSequence X) n p) =
      stagePolyhedralInclusion X n p := by
  exact ConcreteCategory.congr_hom
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (polyhedralSequence X)) (polyhedralUnion_isColimit X) n) p

private theorem polyhedralColimitHomeomorph_inverse_leg (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    (polyhedralColimitHomeomorph X).symm (stagePolyhedralInclusion X n p) =
      colimit.ι (polyhedralSequence X) n p := by
  rw [← polyhedralColimitHomeomorph_leg X n p]
  exact (polyhedralColimitHomeomorph X).symm_apply_apply _

private theorem polyhedralColimitHomeomorph_leg_point (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    (polyhedralColimitHomeomorph X (colimit.ι (polyhedralSequence X) n p)).point =
      p.point.map (stageVertexEmbedding X n) := by
  rw [polyhedralColimitHomeomorph_leg]
  exact stagePolyhedralInclusion_point X n p

private theorem polyhedralUnion_stage_leg (n : ℕ) :
    colimit.ι (polyhedralSequence X) n ≫
        TopCat.ofHom (polyhedralColimitHomeomorph X :
          C(polyhedralUnion X, (unionComplex X).Realization)) =
      TopCat.ofHom (stagePolyhedralInclusion X n) := by
  apply ConcreteCategory.hom_ext
  intro p
  exact polyhedralColimitHomeomorph_leg X n p

end ActualPolyhedralDimensionUnionConstruction

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex PreAbstractSimplicialComplex
open scoped Classical

universe u

namespace ActualPolyhedralRealizationCommonEndConstruction

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

/-- These are the same original sequence: no identification of different stage spaces is assumed. -/
private theorem actual_polyhedralSequence_eq :
    ActualCommonDimensionUnionConstruction.polyhedralSequence X =
      ActualPolyhedralDimensionUnionConstruction.polyhedralSequence X := rfl

/-- The verified colimit homeomorphism uses the same actual sequence chosen for the common end. -/
private def actualSharedPolyhedralHomeomorph :
    ActualCommonDimensionUnionConstruction.polyhedralUnion X ≃ₜ
      (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization := by
  simpa only [ActualCommonDimensionUnionConstruction.polyhedralUnion,
    ActualCommonDimensionUnionConstruction.polyhedralSequence,
    ActualPolyhedralDimensionUnionConstruction.polyhedralUnion,
    ActualPolyhedralDimensionUnionConstruction.polyhedralSequence] using!
      ActualPolyhedralDimensionUnionConstruction.polyhedralColimitHomeomorph X

private theorem actualSharedPolyhedralHomeomorph_leg (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    actualSharedPolyhedralHomeomorph X
        (colimit.ι (ActualCommonDimensionUnionConstruction.polyhedralSequence X) n p) =
      ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n p := by
  simpa only [actualSharedPolyhedralHomeomorph,
    ActualCommonDimensionUnionConstruction.polyhedralUnion,
    ActualCommonDimensionUnionConstruction.polyhedralSequence,
    ActualPolyhedralDimensionUnionConstruction.polyhedralUnion,
    ActualPolyhedralDimensionUnionConstruction.polyhedralSequence] using!
      ActualPolyhedralDimensionUnionConstruction.polyhedralColimitHomeomorph_leg X n p

private theorem actualSharedPolyhedralHomeomorph_inverse_leg (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    (actualSharedPolyhedralHomeomorph X).symm
        (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n p) =
      colimit.ι (ActualCommonDimensionUnionConstruction.polyhedralSequence X) n p := by
  rw [← actualSharedPolyhedralHomeomorph_leg X n p]
  exact (actualSharedPolyhedralHomeomorph X).symm_apply_apply _

private theorem actualSharedPolyhedralHomeomorph_leg_point (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    (actualSharedPolyhedralHomeomorph X
        (colimit.ι (ActualCommonDimensionUnionConstruction.polyhedralSequence X) n p)).point =
      p.point.map (ActualPolyhedralDimensionUnionConstruction.stageVertexEmbedding X n) := by
  rw [actualSharedPolyhedralHomeomorph_leg]
  exact ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion_point X n p

/-- The actual weak-realization end map, using both constructed maps of the same ordinary diagram. -/
private def actualPolyhedralRealizationToCommon :
    C((ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization,
      ActualCommonDimensionUnionConstruction.commonUnion X) :=
  (ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon X).hom.comp
    ((actualSharedPolyhedralHomeomorph X).symm :
      C((ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization,
        ActualCommonDimensionUnionConstruction.polyhedralUnion X))

private theorem actualPolyhedralRealizationToCommon_stage (n : ℕ)
    (p : ((commonSuccessorSystem X).stages n).polyhedron.Realization) :
    actualPolyhedralRealizationToCommon X
        (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n p) =
      ActualCommonDimensionUnionConstruction.commonStageInclusion X n
        (((commonSuccessorSystem X).stages n).polyhedral p) := by
  have hi := actualSharedPolyhedralHomeomorph_inverse_leg X n p
  have hmap := congrArg (fun z : ActualCommonDimensionUnionConstruction.polyhedralUnion X =>
    ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon X z) hi
  exact hmap.trans (ConcreteCategory.congr_hom
    (ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon_stage X n) p)

private theorem actualPolyhedralRealizationToCommon_stage_leg (n : ℕ) :
    TopCat.ofHom (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n) ≫
        TopCat.ofHom (actualPolyhedralRealizationToCommon X) =
      TopCat.ofHom (((commonSuccessorSystem X).stages n).polyhedral) ≫
        ActualCommonDimensionUnionConstruction.commonStageInclusion X n := by
  apply ConcreteCategory.hom_ext
  intro p
  exact actualPolyhedralRealizationToCommon_stage X n p

private theorem actualPolyhedralRealizationToCommon_closed :
    IsClosedEmbedding (actualPolyhedralRealizationToCommon X) :=
  (ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon_isClosedEmbedding X).comp
    (actualSharedPolyhedralHomeomorph X).symm.isClosedEmbedding

private theorem actualPolyhedralRealizationToCommon_range :
    Set.range (actualPolyhedralRealizationToCommon X) =
      Set.range (ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon X) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(actualSharedPolyhedralHomeomorph X).symm x, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨actualSharedPolyhedralHomeomorph X y, ?_⟩
    exact congrArg (fun z : ActualCommonDimensionUnionConstruction.polyhedralUnion X =>
      ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon X z)
        ((actualSharedPolyhedralHomeomorph X).symm_apply_apply y)

private theorem actualPolyhedralRealizationToCommon_image (A :
    Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) :
    actualPolyhedralRealizationToCommon X '' A =
      ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon X ''
        ((actualSharedPolyhedralHomeomorph X).symm '' A) := by
  ext z
  constructor
  · rintro ⟨x, hxA, rfl⟩
    exact ⟨(actualSharedPolyhedralHomeomorph X).symm x, ⟨x, hxA, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hxA, hxy⟩, hyz⟩
    exact ⟨x, hxA, (congrArg
      (ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon X) hxy).trans hyz⟩

private theorem actualPolyhedralRealizationToCommon_image_stage (n : ℕ)
    (A : Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) :
    (ActualCommonDimensionUnionConstruction.commonStageInclusion X n) ⁻¹'
        (actualPolyhedralRealizationToCommon X '' A) =
      ((commonSuccessorSystem X).stages n).polyhedral ''
        ((ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n) ⁻¹' A) := by
  have hpre :
      (colimit.ι (ActualCommonDimensionUnionConstruction.polyhedralSequence X) n) ⁻¹'
          ((actualSharedPolyhedralHomeomorph X).symm '' A) =
        (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n) ⁻¹' A := by
    ext p
    constructor
    · rintro ⟨x, hxA, hxp⟩
      have h := congrArg (actualSharedPolyhedralHomeomorph X) hxp
      have heq : x = ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n p :=
        ((actualSharedPolyhedralHomeomorph X).apply_symm_apply x).symm.trans
          (h.trans (actualSharedPolyhedralHomeomorph_leg X n p))
      exact Eq.mp (congrArg (fun z :
        (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization => z ∈ A) heq) hxA
    · intro hpA
      exact ⟨ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n p,
        hpA, actualSharedPolyhedralHomeomorph_inverse_leg X n p⟩
  have h₁ := congrArg (fun B : Set (ActualCommonDimensionUnionConstruction.commonUnion X) =>
    (ActualCommonDimensionUnionConstruction.commonStageInclusion X n) ⁻¹' B)
      (actualPolyhedralRealizationToCommon_image X A)
  have h₂ := ActualCommonDimensionUnionConstruction.polyhedralUnionToCommon_image_stage X n
    ((actualSharedPolyhedralHomeomorph X).symm '' A)
  have h₃ := congrArg (fun B :
      Set ((ActualCommonDimensionUnionConstruction.polyhedralSequence X).obj n) =>
    ((commonSuccessorSystem X).stages n).polyhedral '' B) hpre
  exact h₁.trans (h₂.trans h₃)

/-- The actual two ends meet exactly in the literal common initial stage. -/
private theorem actualRealization_global_end_intersection :
    Set.range (ActualCommonDimensionUnionConstruction.originalXToCommon X) ∩
        Set.range (actualPolyhedralRealizationToCommon X) =
      Set.range (ActualCommonDimensionUnionConstruction.commonStageInclusion X 0) := by
  rw [actualPolyhedralRealizationToCommon_range]
  exact ActualCommonDimensionUnionConstruction.commonUnion_end_intersection X

end ActualPolyhedralRealizationCommonEndConstruction

end

noncomputable section

open CategoryTheory Topology Topology.CWComplex PreAbstractSimplicialComplex
open scoped Classical

universe u

namespace ActualCanonicalPolyhedralUnionCellCoverage

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

/-- The exact previously constructed canonical cell law, instantiated on the actual stage image. -/
private def actualStageCanonicalCellData (n : ℕ) :
    Σ' κ : ∀ m,
      cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m ↪
        cell (Set.univ : Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) m,
      ∀ (m : ℕ)
        (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m)
        (q : (classicalCellDiskPair.{u} m).fst),
        ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n
            (map m a q.down.val) = map m (κ m a) q.down.val := by
  let d := Realization.classicalCellEmbeddingOfRelabelInclusion
    ((commonSuccessorSystem X).stages n).polyhedron
    (ActualPolyhedralDimensionUnionConstruction.stageVertexEmbedding X n)
    (ActualPolyhedralDimensionUnionConstruction.unionComplex X)
    (ActualPolyhedralDimensionUnionConstruction.mappedStageComplex_le_union X n)
  refine ⟨d.fst, ?_⟩
  intro m a q
  exact d.snd m a q

private def actualStageCanonicalCellEmbedding (n m : ℕ) :
    cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m ↪
      cell (Set.univ : Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) m :=
  (actualStageCanonicalCellData X n).fst m

private theorem actualStageCanonicalCellEmbedding_disk (n m : ℕ)
    (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m)
    (q : (classicalCellDiskPair.{u} m).fst) :
    ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n
        (map m a q.down.val) = map m (actualStageCanonicalCellEmbedding X n m a) q.down.val :=
  (actualStageCanonicalCellData X n).snd m a q

/-- The matching image uses the selected CW structures of the actual stage and union realizations. -/
private def actualStageCanonicalMatching (n : ℕ) :
    Topology.CWComplex.MatchedAmalgam.MatchingCharacteristicData
      (𝟙 (TopCat.of ((commonSuccessorSystem X).stages n).polyhedron.Realization))
      (TopCat.ofHom (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n)) where
  leftLabels := fun _ => Function.Embedding.refl _
  rightLabels := (actualStageCanonicalCellData X n).fst
  leftLaw := fun _ _ _ => rfl
  rightLaw m a q := (actualStageCanonicalCellData X n).snd m a (ULift.up q)

private def actualStageCanonicalSubcomplex (n : ℕ) :
    Subcomplex (Set.univ : Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) :=
  Topology.CWComplex.MatchedAmalgam.matchingRightSubcomplex
    (actualStageCanonicalMatching X n)
    (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion_closed X n)

private theorem actualStageCanonicalSubcomplex_carrier (n : ℕ) :
    (actualStageCanonicalSubcomplex X n :
      Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) =
        Set.range (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n) :=
  Topology.CWComplex.MatchedAmalgam.matchingRightSubcomplex_carrier
    (actualStageCanonicalMatching X n)
    (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion_closed X n)

private theorem actualStageCanonicalSubcomplex_labels (n m : ℕ) :
    (actualStageCanonicalSubcomplex X n).I m =
      Set.range (actualStageCanonicalCellEmbedding X n m) :=
  Topology.CWComplex.MatchedAmalgam.matchingRightSubcomplex_I
    (actualStageCanonicalMatching X n)
    (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion_closed X n) m

/-- Every selected canonical union cell comes from the SAME stage cell embedding. -/
private theorem actualCanonicalUnionCell_covered (m : ℕ)
    (b : cell (Set.univ : Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) m) :
    ∃ (n : ℕ)
      (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m),
      actualStageCanonicalCellEmbedding X n m a = b := by
  let y : (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization :=
    map m b (0 : Fin m → ℝ)
  obtain ⟨n, p, hpy⟩ := ActualPolyhedralDimensionUnionConstruction.unionPoint_stageLift X y
  have hyStage : y ∈ (actualStageCanonicalSubcomplex X n :
      Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) := by
    rw [actualStageCanonicalSubcomplex_carrier]
    exact ⟨p, hpy⟩
  have hyCenter : y ∈ openCell
      (C := (Set.univ : Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization)) m b := by
    refine ⟨0, by simp, ?_⟩
    simp only [y, Topology.CWComplex.map_def]
  have hb : b ∈ (actualStageCanonicalSubcomplex X n).I m := by
    by_contra hnot
    exact ((actualStageCanonicalSubcomplex X n).disjoint_openCell_subcomplex_of_notMem hnot).notMem_of_mem_left
      hyCenter hyStage
  rw [actualStageCanonicalSubcomplex_labels] at hb
  obtain ⟨a, ha⟩ := hb
  exact ⟨n, a, ha⟩


example (m : ℕ)
    (b : cell (Set.univ : Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) m) :
    ∃ (n : ℕ)
      (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m),
      actualStageCanonicalCellEmbedding X n m a = b :=
  actualCanonicalUnionCell_covered X m b

example (n m : ℕ)
    (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m)
    (q : (classicalCellDiskPair.{u} m).fst) :
    ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n
        (map m a q.down.val) = map m (actualStageCanonicalCellEmbedding X n m a) q.down.val :=
  actualStageCanonicalCellEmbedding_disk X n m a q

example (n m : ℕ) :
    (actualStageCanonicalSubcomplex X n :
      Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) =
        Set.range (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n) ∧
    (actualStageCanonicalSubcomplex X n).I m =
      Set.range (actualStageCanonicalCellEmbedding X n m) :=
  ⟨actualStageCanonicalSubcomplex_carrier X n, actualStageCanonicalSubcomplex_labels X n m⟩

end ActualCanonicalPolyhedralUnionCellCoverage

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
open PreAbstractSimplicialComplex
open ActualCanonicalPolyhedralUnionCellCoverage

universe u

namespace ActualCommonDimensionUnionCWDictionary

private theorem cellCenter_injective {Y : Type u} [TopologicalSpace Y]
    [CWComplex (Set.univ : Set Y)] (m : ℕ)
    {a b : cell (Set.univ : Set Y) m}
    (h : map (C := (Set.univ : Set Y)) m a (0 : Fin m → ℝ) =
      map (C := (Set.univ : Set Y)) m b 0) : a = b := by
  by_contra hne
  have hs : (⟨m, a⟩ : Σ n, cell (Set.univ : Set Y) n) ≠ ⟨m, b⟩ := by
    intro heq
    exact hne (sigma_mk_injective heq)
  have hd := disjoint_openCell_of_ne (C := (Set.univ : Set Y)) hs
  have ha : map (C := (Set.univ : Set Y)) m a 0 ∈
      openCell (C := (Set.univ : Set Y)) m a := by
    refine ⟨0, by simp, ?_⟩
    simp only [Topology.CWComplex.map_def]
  have hb : map (C := (Set.univ : Set Y)) m a 0 ∈
      openCell (C := (Set.univ : Set Y)) m b := by
    refine ⟨0, by simp, ?_⟩
    simpa only [Topology.CWComplex.map_def] using h.symm
  exact hd.notMem_of_mem_left ha hb

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

@[instance_reducible]
private def actualCommonCW :
    CWComplex (Set.univ : Set (ActualCommonDimensionUnionConstruction.commonUnion X)) := by
  change CWComplex (Set.univ : Set
    (CommonUnionCWBirthPreparation.unionSpace (commonSuccessorSystem X)))
  exact CommonUnionCWBirthPreparation.unionClassicalCW (commonSuccessorSystem X)

private theorem actualCommonT2 :
    T2Space (ActualCommonDimensionUnionConstruction.commonUnion X) := by
  change T2Space (CommonUnionCWBirthPreparation.unionSpace (commonSuccessorSystem X))
  exact CommonUnionCWBirthPreparation.HausdorffUnion.actualCommonUnionHausdorff X

private abbrev canonicalPolyCell (m : ℕ) :=
  cell (Set.univ : Set (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) m

private def commonCell (m : ℕ) : Type u :=
  letI := actualCommonCW X
  cell (Set.univ : Set (ActualCommonDimensionUnionConstruction.commonUnion X)) m

private def stageCommonCellEmbedding (n m : ℕ) :
    letI := ((commonSuccessorSystem X).stages n).cw
    cell (Set.univ : Set ((commonSuccessorSystem X).stages n).space) m ↪ commonCell X m := by
  letI := ((commonSuccessorSystem X).stages n).cw
  letI := actualCommonCW X
  exact CommonUnionCWBirthPreparation.stageCellIntoUnion (commonSuccessorSystem X) n m

private theorem stageCommonCellEmbedding_disk (n m : ℕ) :
    letI := ((commonSuccessorSystem X).stages n).cw
    letI := actualCommonCW X
    ∀ (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).space) m)
      (q : (classicalCellDiskPair.{u} m).fst),
      ActualCommonDimensionUnionConstruction.commonStageInclusion X n
          (map (C := (Set.univ : Set ((commonSuccessorSystem X).stages n).space)) m a q.down.val) =
        map (C := (Set.univ : Set (ActualCommonDimensionUnionConstruction.commonUnion X))) m
          (stageCommonCellEmbedding X n m a) q.down.val := by
  let := ((commonSuccessorSystem X).stages n).cw
  let := actualCommonCW X
  intro a q
  simpa only [TopCat.comp_app, characteristicDiskMap_apply] using!
    (ConcreteCategory.congr_hom
      (CommonUnionCWBirthPreparation.unionCharacteristicDisk_stage
        (commonSuccessorSystem X) n m a) q).symm

private def stageCanonicalEndLabel (n m : ℕ)
    (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m) :
    commonCell X m := by
  letI := ((commonSuccessorSystem X).stages n).cw
  exact stageCommonCellEmbedding X n m
    (((commonSuccessorSystem X).stages n).polyhedralLabels m a)

private theorem stageCanonicalEndLabel_disk (n m : ℕ)
    (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m)
    (q : (classicalCellDiskPair.{u} m).fst) :
    letI := actualCommonCW X
    ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X
        (map (C := (Set.univ : Set
          (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization)) m
            (actualStageCanonicalCellEmbedding X n m a) q.down.val) =
      map (C := (Set.univ : Set (ActualCommonDimensionUnionConstruction.commonUnion X))) m
        (stageCanonicalEndLabel X n m a) q.down.val := by
  let := actualCommonCW X
  let := ((commonSuccessorSystem X).stages n).cw
  have hstage : ((commonSuccessorSystem X).stages n).polyhedral
        (map (C := (Set.univ : Set
          ((commonSuccessorSystem X).stages n).polyhedron.Realization)) m a q.down.val) =
      map (C := (Set.univ : Set ((commonSuccessorSystem X).stages n).space)) m
        (((commonSuccessorSystem X).stages n).polyhedralLabels m a) q.down.val := by
    simpa only [TopCat.comp_app, characteristicDiskMap_apply] using!
      ConcreteCategory.congr_hom
        (((commonSuccessorSystem X).stages n).polyhedral_characteristicDiskMap m a) q
  calc
    _ = ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X
        (ActualPolyhedralDimensionUnionConstruction.stagePolyhedralInclusion X n
          (map (C := (Set.univ : Set
            ((commonSuccessorSystem X).stages n).polyhedron.Realization)) m a q.down.val)) :=
      congrArg
        (ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X)
        (actualStageCanonicalCellEmbedding_disk X n m a q).symm
    _ = ActualCommonDimensionUnionConstruction.commonStageInclusion X n
        (((commonSuccessorSystem X).stages n).polyhedral
          (map (C := (Set.univ : Set
            ((commonSuccessorSystem X).stages n).polyhedron.Realization)) m a q.down.val)) :=
      ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon_stage X n _
    _ = ActualCommonDimensionUnionConstruction.commonStageInclusion X n
        (map (C := (Set.univ : Set ((commonSuccessorSystem X).stages n).space)) m
          (((commonSuccessorSystem X).stages n).polyhedralLabels m a) q.down.val) :=
      congrArg (ActualCommonDimensionUnionConstruction.commonStageInclusion X n) hstage
    _ = _ := stageCommonCellEmbedding_disk X n m _ q

private def canonicalCellLift (m : ℕ) (b : canonicalPolyCell X m) :
    Σ n : ℕ, {a : cell (Set.univ : Set
      ((commonSuccessorSystem X).stages n).polyhedron.Realization) m //
        actualStageCanonicalCellEmbedding X n m a = b} := by
  classical
  let h := actualCanonicalUnionCell_covered X m b
  let n := Classical.choose h
  let hn := Classical.choose_spec h
  exact ⟨n, Classical.choose hn, Classical.choose_spec hn⟩

private def canonicalEndLabel (m : ℕ) (b : canonicalPolyCell X m) : commonCell X m :=
  stageCanonicalEndLabel X (canonicalCellLift X m b).fst m (canonicalCellLift X m b).snd.val

private theorem canonicalEndLabel_disk (m : ℕ) (b : canonicalPolyCell X m)
    (q : (classicalCellDiskPair.{u} m).fst) :
    letI := actualCommonCW X
    ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X
        (map (C := (Set.univ : Set
          (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization)) m b q.down.val) =
      map (C := (Set.univ : Set (ActualCommonDimensionUnionConstruction.commonUnion X))) m
        (canonicalEndLabel X m b) q.down.val := by
  let := actualCommonCW X
  let L := canonicalCellLift X m b
  have h : actualStageCanonicalCellEmbedding X L.fst m L.snd.val = b := L.snd.property
  have hd := stageCanonicalEndLabel_disk X L.fst m L.snd.val q
  exact (congrArg
    (fun c : canonicalPolyCell X m =>
      ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X
        (map (C := (Set.univ : Set
          (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization)) m c q.down.val))
      h).symm.trans hd


private theorem canonicalEndLabel_injective (m : ℕ) :
    Function.Injective (canonicalEndLabel X m) := by
  let := actualCommonCW X
  intro a b hab
  let q : (classicalCellDiskPair.{u} m).fst := ULift.up ⟨0, by simp⟩
  have hmap : ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X
        (map (C := (Set.univ : Set
          (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization)) m a 0) =
      ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X
        (map (C := (Set.univ : Set
          (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization)) m b 0) :=
    (canonicalEndLabel_disk X m a q).trans
      ((congrArg
        (fun c : commonCell X m => map
          (C := (Set.univ : Set (ActualCommonDimensionUnionConstruction.commonUnion X))) m c 0)
        hab).trans (canonicalEndLabel_disk X m b q).symm)
  exact cellCenter_injective m
    ((ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon_closed X).injective
      hmap)

private def canonicalEndEmbedding (m : ℕ) : canonicalPolyCell X m ↪ commonCell X m :=
  ⟨canonicalEndLabel X m, canonicalEndLabel_injective X m⟩

private theorem canonicalEndEmbedding_stage (n m : ℕ)
    (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m) :
    canonicalEndEmbedding X m (actualStageCanonicalCellEmbedding X n m a) =
      stageCanonicalEndLabel X n m a := by
  let := actualCommonCW X
  let q : (classicalCellDiskPair.{u} m).fst := ULift.up ⟨0, by simp⟩
  apply cellCenter_injective m
  exact (canonicalEndLabel_disk X m (actualStageCanonicalCellEmbedding X n m a) q).symm.trans
    (stageCanonicalEndLabel_disk X n m a q)

private theorem canonicalEndEmbedding_characteristicDiskMap (m : ℕ) (b : canonicalPolyCell X m) :
    letI := actualCommonCW X
    characteristicDiskMap (X := TopCat.of
        (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) m b ≫
      TopCat.ofHom
        (ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X) =
      characteristicDiskMap (X := ActualCommonDimensionUnionConstruction.commonUnion X) m
        (canonicalEndEmbedding X m b) := by
  let := actualCommonCW X
  apply TopCat.ext
  intro q
  simpa only [TopCat.comp_app, characteristicDiskMap_apply] using!
    canonicalEndLabel_disk X m b q

private def canonicalPolyhedralMatching :
    letI := actualCommonCW X
    MatchedAmalgam.MatchingCharacteristicData
      (𝟙 (TopCat.of (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization))
      (TopCat.ofHom
        (ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X)) := by
  letI := actualCommonCW X
  exact
    { leftLabels := fun _ => Function.Embedding.refl _
      rightLabels := canonicalEndEmbedding X
      leftLaw := fun _ _ _ => rfl
      rightLaw := fun m b q => canonicalEndLabel_disk X m b (ULift.up q) }

private def canonicalPolyhedralEndSubcomplex :
    letI := actualCommonCW X
    Subcomplex (Set.univ : Set (ActualCommonDimensionUnionConstruction.commonUnion X)) := by
  letI := actualCommonCW X
  exact MatchedAmalgam.matchingRightSubcomplex (canonicalPolyhedralMatching X)
    (ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon_closed X)

private theorem canonicalPolyhedralEndSubcomplex_carrier :
    letI := actualCommonCW X
    (canonicalPolyhedralEndSubcomplex X :
      Set (ActualCommonDimensionUnionConstruction.commonUnion X)) =
      Set.range (ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X) := by
  let := actualCommonCW X
  exact MatchedAmalgam.matchingRightSubcomplex_carrier (canonicalPolyhedralMatching X)
    (ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon_closed X)

private theorem canonicalPolyhedralEndSubcomplex_labels (m : ℕ) :
    letI := actualCommonCW X
    (canonicalPolyhedralEndSubcomplex X).I m = Set.range (canonicalEndEmbedding X m) := by
  let := actualCommonCW X
  exact MatchedAmalgam.matchingRightSubcomplex_I (canonicalPolyhedralMatching X)
    (ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon_closed X) m

private theorem canonicalPolyhedralEndSubcomplex_stage_image (m : ℕ) :
    letI := actualCommonCW X
    (canonicalPolyhedralEndSubcomplex X).I m =
      ⋃ n : ℕ, Set.range (stageCanonicalEndLabel X n m) := by
  let := actualCommonCW X
  rw [canonicalPolyhedralEndSubcomplex_labels]
  ext c
  constructor
  · rintro ⟨b, hb⟩
    let L := canonicalCellLift X m b
    exact Set.mem_iUnion.mpr ⟨L.fst, L.snd.val, hb⟩
  · intro hc
    rcases Set.mem_iUnion.mp hc with ⟨n, a, ha⟩
    exact ⟨actualStageCanonicalCellEmbedding X n m a,
      (canonicalEndEmbedding_stage X n m a).trans ha⟩


example : CWComplex (Set.univ : Set (ActualCommonDimensionUnionConstruction.commonUnion X)) :=
  actualCommonCW X

example : T2Space (ActualCommonDimensionUnionConstruction.commonUnion X) :=
  actualCommonT2 X

example (n m : ℕ)
    (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m) :
    canonicalEndEmbedding X m (actualStageCanonicalCellEmbedding X n m a) =
      stageCanonicalEndLabel X n m a := canonicalEndEmbedding_stage X n m a

example (m : ℕ) (b : canonicalPolyCell X m) :
    letI := actualCommonCW X
    characteristicDiskMap (X := TopCat.of
        (ActualPolyhedralDimensionUnionConstruction.unionComplex X).Realization) m b ≫
      TopCat.ofHom
        (ActualPolyhedralRealizationCommonEndConstruction.actualPolyhedralRealizationToCommon X) =
      characteristicDiskMap (X := ActualCommonDimensionUnionConstruction.commonUnion X) m
        (canonicalEndEmbedding X m b) := canonicalEndEmbedding_characteristicDiskMap X m b

end ActualCommonDimensionUnionCWDictionary

end


public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open scoped Classical

universe u v
namespace Topology.CWComplex

/-- The actual common dimension union, its selected CW structure, and both constructed ends. -/
structure CommonDimensionUnionData (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] where
  /-- A cocone over the sequence of common successor stage spaces and their transitions. -/
  commonCocone : Cocone (Functor.ofSequence
    (X := fun n => ((commonSuccessorSystem X).stages n).space)
    (fun n => TopCat.ofHom ((commonSuccessorSystem X).transition n)))
  /-- `commonCocone` is a colimit cocone. -/
  common_isColimit : IsColimit commonCocone
  /-- The CW structure selected on the common union `commonCocone.pt`. -/
  commonCW : CWComplex (Set.univ : Set commonCocone.pt)
  commonT2 : T2Space commonCocone.pt
  commonStage_closed : ∀ n, IsClosedEmbedding (commonCocone.ι.app n).hom
  /-- The map from the disjoint union of all stage spaces to the common union, given on
  each summand by the cocone leg (`commonSigmaQuotient_value`). -/
  commonSigmaQuotient : C((Σ n : ℕ, ((commonSuccessorSystem X).stages n).space), commonCocone.pt)
  commonSigmaQuotient_value : ∀ n x, commonSigmaQuotient ⟨n, x⟩ = commonCocone.ι.app n x
  commonSigmaQuotient_isQuotientMap : IsQuotientMap commonSigmaQuotient
  common_continuous_iff : ∀ {Y : Type v} [TopologicalSpace Y] (f : commonCocone.pt → Y),
    Continuous f ↔ ∀ n, Continuous (f ∘ commonCocone.ι.app n)
  common_isClosed_iff : ∀ A : Set commonCocone.pt,
    IsClosed A ↔ ∀ n, IsClosed ((commonCocone.ι.app n) ⁻¹' A)
  /-- For each stage `n` and dimension `m`, the embedding of the stage-`n` `m`-cells into
  the `m`-cells of the common union. -/
  commonStageLabels :
    letI := commonCW
    ∀ n, letI := ((commonSuccessorSystem X).stages n).cw
    ∀ m, cell (Set.univ : Set ((commonSuccessorSystem X).stages n).space) m ↪
      cell (Set.univ : Set commonCocone.pt) m
  /-- For each stage `n`, the subcomplex of the common union whose carrier is the range
  of the stage-`n` cocone leg (`commonStageSubcomplex_carrier`). -/
  commonStageSubcomplex :
    letI := commonCW
    ∀ n, Subcomplex (Set.univ : Set commonCocone.pt)
  commonStageSubcomplex_carrier :
    letI := commonCW
    ∀ n, (commonStageSubcomplex n : Set commonCocone.pt) = Set.range (commonCocone.ι.app n)
  commonStageSubcomplex_labels :
    letI := commonCW
    ∀ n, letI := ((commonSuccessorSystem X).stages n).cw
    ∀ m, (commonStageSubcomplex n).I m = Set.range (commonStageLabels n m)
  commonStage_characteristicDiskMap :
    letI := commonCW
    ∀ n, letI := ((commonSuccessorSystem X).stages n).cw
    ∀ m (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).space) m),
    characteristicDiskMap (X := ((commonSuccessorSystem X).stages n).space) m a ≫ commonCocone.ι.app n =
      characteristicDiskMap (X := commonCocone.pt) m (commonStageLabels n m a)
  commonStageLabels_step :
    letI := commonCW
    ∀ n, letI := ((commonSuccessorSystem X).stages n).cw
    letI := ((commonSuccessorSystem X).stages (n + 1)).cw
    ∀ m (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).space) m),
      commonStageLabels (n + 1) m ((commonSuccessorSystem X).oldStageLabels n m a) = commonStageLabels n m a
  /-- A cocone over the sequence of stage vertex types and their vertex transitions. -/
  vertexCocone : Cocone (Functor.ofSequence
    (X := fun n => ((commonSuccessorSystem X).stages n).vertices)
    (fun n => TypeCat.ofHom (commonSuccessorSystemVertexTransition X n)))
  /-- `vertexCocone` is a colimit cocone. -/
  vertex_isColimit : IsColimit vertexCocone
  /-- For each stage `n`, the embedding of the stage-`n` vertices into the union vertices;
  it agrees with the cocone leg (`stageVertexEmbedding_leg`). -/
  stageVertexEmbedding : ∀ n, ((commonSuccessorSystem X).stages n).vertices ↪ vertexCocone.pt
  stageVertexEmbedding_leg : ∀ n v, stageVertexEmbedding n v = vertexCocone.ι.app n v
  stageVertexEmbedding_step : ∀ n,
    (commonSuccessorSystemVertexTransition X n).trans (stageVertexEmbedding (n + 1)) = stageVertexEmbedding n
  /-- The union simplicial complex on the union vertices, whose faces are the images of
  the stage faces (`polyhedron_faces`). -/
  polyhedron : PreAbstractSimplicialComplex vertexCocone.pt
  polyhedron_faces : ∀ s, s ∈ polyhedron ↔ ∃ (n : ℕ)
    (a : Finset ((commonSuccessorSystem X).stages n).vertices),
      a ∈ ((commonSuccessorSystem X).stages n).polyhedron ∧ a.map (stageVertexEmbedding n) = s
  /-- For each stage `n`, the map from the stage-`n` polyhedral realization to the
  realization of `polyhedron`. -/
  polyhedralStageInclusion : ∀ n, C(((commonSuccessorSystem X).stages n).polyhedron.Realization, polyhedron.Realization)
  polyhedralStageInclusion_point : ∀ n p,
    (polyhedralStageInclusion n p).point = p.point.map (stageVertexEmbedding n)
  polyhedralStageInclusion_closed : ∀ n, IsClosedEmbedding (polyhedralStageInclusion n)
  polyhedralStageInclusion_step : ∀ n p,
    polyhedralStageInclusion (n + 1) ((commonSuccessorSystem X).polyhedralTransition n p) = polyhedralStageInclusion n p
  polyhedralPoint_stageLift : ∀ x : polyhedron.Realization, ∃ n p, polyhedralStageInclusion n p = x
  polyhedron_continuous_iff : ∀ {Y : Type v} [TopologicalSpace Y] (f : polyhedron.Realization → Y),
    Continuous f ↔ ∀ n, Continuous (f ∘ polyhedralStageInclusion n)
  polyhedron_isClosed_iff : ∀ A : Set polyhedron.Realization,
    IsClosed A ↔ ∀ n, IsClosed ((polyhedralStageInclusion n) ⁻¹' A)
  /-- A homeomorphism from the colimit of the stage polyhedral realizations to the
  realization of `polyhedron`, matching the stage legs with
  `polyhedralStageInclusion`. -/
  polyhedralColimitHomeomorph :
    (colimit (Functor.ofSequence
      (X := fun n => TopCat.of (((commonSuccessorSystem X).stages n).polyhedron.Realization))
      (fun n => TopCat.ofHom ((commonSuccessorSystem X).polyhedralTransition n))) : TopCat.{u}) ≃ₜ
      polyhedron.Realization
  polyhedralColimitHomeomorph_leg : ∀ n p,
    polyhedralColimitHomeomorph
      (colimit.ι (Functor.ofSequence
        (X := fun n => TopCat.of (((commonSuccessorSystem X).stages n).polyhedron.Realization))
        (fun n => TopCat.ofHom ((commonSuccessorSystem X).polyhedralTransition n))) n p) =
      polyhedralStageInclusion n p
  polyhedralColimitHomeomorph_inverse_leg : ∀ n p,
    polyhedralColimitHomeomorph.symm (polyhedralStageInclusion n p) =
      colimit.ι (Functor.ofSequence
        (X := fun n => TopCat.of (((commonSuccessorSystem X).stages n).polyhedron.Realization))
        (fun n => TopCat.ofHom ((commonSuccessorSystem X).polyhedralTransition n))) n p
  /-- For each stage `n` and dimension `m`, the embedding of the stage-`n` polyhedral
  `m`-cells into the `m`-cells of the realization of `polyhedron`. -/
  polyhedralStageCellLabels : ∀ n m,
    cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m ↪
      cell (Set.univ : Set polyhedron.Realization) m
  polyhedralStageCell_characteristicDiskMap : ∀ n m
    (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m),
    characteristicDiskMap (X := TopCat.of (((commonSuccessorSystem X).stages n).polyhedron.Realization)) m a ≫
      TopCat.ofHom (polyhedralStageInclusion n) =
        characteristicDiskMap (X := TopCat.of polyhedron.Realization) m (polyhedralStageCellLabels n m a)
  polyhedralStageCell_covered : ∀ m (b : cell (Set.univ : Set polyhedron.Realization) m),
    ∃ n a, polyhedralStageCellLabels n m a = b
  /-- The map from the original space `X` into the common union, a closed embedding
  (`originalEnd_closed`). -/
  originalEnd : C(X, commonCocone.pt)
  originalEnd_closed : IsClosedEmbedding originalEnd
  originalEnd_stage : ∀ n x, originalEnd (skeletonInclusion X (n + 1) x) =
    commonCocone.ι.app n (((commonSuccessorSystem X).stages n).original x)
  originalEnd_image_stage : ∀ n (A : Set X),
    (commonCocone.ι.app n) ⁻¹' (originalEnd '' A) =
      ((commonSuccessorSystem X).stages n).original '' ((skeletonInclusion X (n + 1)) ⁻¹' A)
  /-- The map from the realization of `polyhedron` into the common union, a closed
  embedding (`polyhedralEnd_closed`). -/
  polyhedralEnd : C(polyhedron.Realization, commonCocone.pt)
  polyhedralEnd_closed : IsClosedEmbedding polyhedralEnd
  polyhedralEnd_stage : ∀ n p,
    polyhedralEnd (polyhedralStageInclusion n p) =
      commonCocone.ι.app n (((commonSuccessorSystem X).stages n).polyhedral p)
  polyhedralEnd_image_stage : ∀ n (A : Set polyhedron.Realization),
    (commonCocone.ι.app n) ⁻¹' (polyhedralEnd '' A) =
      ((commonSuccessorSystem X).stages n).polyhedral '' ((polyhedralStageInclusion n) ⁻¹' A)
  global_end_intersection : Set.range originalEnd ∩ Set.range polyhedralEnd = Set.range (commonCocone.ι.app 0)
  /-- A homeomorphism from `skeletonTop X 1` to the stage-0 space that agrees with the
  stage-0 original map (`initialOriginalHomeomorph_original`). -/
  initialOriginalHomeomorph : skeletonTop X 1 ≃ₜ ((commonSuccessorSystem X).stages 0).space
  initialOriginalHomeomorph_original :
    ((commonSuccessorSystem X).stages 0).original = (initialOriginalHomeomorph : C(_, _))
  /-- An equivalence between the stage-0 vertices and the 0-cells of `X`, equal to the
  successor system's `initialVertices`. -/
  initialVertices : ((commonSuccessorSystem X).stages 0).vertices ≃ cell (Set.univ : Set X) 0
  initialVertices_eq : initialVertices = (commonSuccessorSystem X).initialVertices
  initial_original_value : ∀ z : skeletonTop X 1,
    originalEnd (skeletonInclusion X 1 z) = commonCocone.ι.app 0 (initialOriginalHomeomorph z)
  global_zero_intersection :
    Set.range originalEnd ∩ Set.range polyhedralEnd =
      Set.range (fun z : skeletonTop X 1 => originalEnd (skeletonInclusion X 1 z))
  /-- For each 0-cell `j` of `X`, the point of the realization of `polyhedron` included
  from stage 0 (`zeroPolyhedral_initial`). -/
  zeroPolyhedral : ∀ j : cell (Set.univ : Set X) 0, polyhedron.Realization
  zeroPolyhedral_initial : ∀ j, zeroPolyhedral j =
    polyhedralStageInclusion 0 ((commonSuccessorSystem X).zeroPolyhedral j 0)
  zero_ends_value : ∀ j, polyhedralEnd (zeroPolyhedral j) = originalEnd (map (C := (Set.univ : Set X)) 0 j 0)
  /-- For each dimension `m`, the embedding of the `m`-cells of the realization of
  `polyhedron` into the `m`-cells of the common union. -/
  polyhedralEndLabels :
    letI := commonCW
    ∀ m, cell (Set.univ : Set polyhedron.Realization) m ↪ cell (Set.univ : Set commonCocone.pt) m
  /-- The subcomplex of the common union whose carrier is the range of `polyhedralEnd`
  (`polyhedralEndSubcomplex_carrier`). -/
  polyhedralEndSubcomplex :
    letI := commonCW
    Subcomplex (Set.univ : Set commonCocone.pt)
  polyhedralEndSubcomplex_carrier :
    letI := commonCW
    (polyhedralEndSubcomplex : Set commonCocone.pt) = Set.range polyhedralEnd
  polyhedralEndSubcomplex_labels :
    letI := commonCW
    ∀ m, polyhedralEndSubcomplex.I m = Set.range (polyhedralEndLabels m)
  polyhedralEnd_characteristicDiskMap :
    letI := commonCW
    ∀ m (b : cell (Set.univ : Set polyhedron.Realization) m),
      characteristicDiskMap (X := TopCat.of polyhedron.Realization) m b ≫ TopCat.ofHom polyhedralEnd =
        characteristicDiskMap (X := commonCocone.pt) m (polyhedralEndLabels m b)
  polyhedralEndLabels_stage :
    letI := commonCW
    ∀ n, letI := ((commonSuccessorSystem X).stages n).cw
    ∀ m (a : cell (Set.univ : Set ((commonSuccessorSystem X).stages n).polyhedron.Realization) m),
      polyhedralEndLabels m (polyhedralStageCellLabels n m a) =
        commonStageLabels n m (((commonSuccessorSystem X).stages n).polyhedralLabels m a)
  polyhedralEndSubcomplex_stage_image :
    letI := commonCW
    ∀ m, polyhedralEndSubcomplex.I m = ⋃ n, Set.range (fun a =>
      commonStageLabels n m (((commonSuccessorSystem X).stages n).polyhedralLabels m a))

attribute [nolint defsWithUnderscore] CommonDimensionUnionData.common_isColimit
attribute [nolint defsWithUnderscore] CommonDimensionUnionData.vertex_isColimit

end Topology.CWComplex
end

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology PreAbstractSimplicialComplex
open ActualCommonDimensionUnionConstruction ActualPolyhedralDimensionUnionConstruction
open ActualPolyhedralRealizationCommonEndConstruction ActualCanonicalPolyhedralUnionCellCoverage
open ActualCommonDimensionUnionCWDictionary

universe u v
namespace Topology.CWComplex

/-- Construct every actual union, cell, comparison, and end datum from the original Hausdorff CW space. -/
def commonDimensionUnion (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)] :
    CommonDimensionUnionData.{u, v} X := by
  let S := commonSuccessorSystem X
  refine
    { commonCocone := colimit.cocone (ActualCommonDimensionUnionConstruction.commonSequence X)
      common_isColimit := by exact colimit.isColimit _
      commonCW := actualCommonCW X
      commonT2 := actualCommonT2 X
      commonStage_closed := commonStageInclusion_closed X
      commonSigmaQuotient := (commonStageSigmaQuotient X).hom
      commonSigmaQuotient_value := fun _ _ => rfl
      commonSigmaQuotient_isQuotientMap := isQuotientMap_commonStageSigmaQuotient X
      common_continuous_iff := fun f => commonUnion_continuous_iff X f
      common_isClosed_iff := commonUnion_isClosed_iff X
      commonStageLabels := stageCommonCellEmbedding X
      commonStageSubcomplex := CommonUnionCWBirthPreparation.unionStageSubcomplex S
      commonStageSubcomplex_carrier := CommonUnionCWBirthPreparation.unionStageSubcomplex_carrier S
      commonStageSubcomplex_labels := CommonUnionCWBirthPreparation.unionStageSubcomplex_labels S
      commonStage_characteristicDiskMap := by
        intro n m a
        exact (CommonUnionCWBirthPreparation.unionCharacteristicDisk_stage S n m a).symm
      commonStageLabels_step := by
        intro n m a
        exact CommonUnionCWBirthPreparation.stageCellIntoUnion_step S n m a
      vertexCocone := colimit.cocone (vertexSequence X)
      vertex_isColimit := by exact colimit.isColimit _
      stageVertexEmbedding := ActualPolyhedralDimensionUnionConstruction.stageVertexEmbedding X
      stageVertexEmbedding_leg := fun _ _ => rfl
      stageVertexEmbedding_step := stageVertexEmbedding_successor X
      polyhedron := unionComplex X
      polyhedron_faces := unionComplex_exact_stage_images X
      polyhedralStageInclusion := stagePolyhedralInclusion X
      polyhedralStageInclusion_point := stagePolyhedralInclusion_point X
      polyhedralStageInclusion_closed := stagePolyhedralInclusion_closed X
      polyhedralStageInclusion_step := stagePolyhedralInclusion_successor X
      polyhedralPoint_stageLift := unionPoint_stageLift X
      polyhedron_continuous_iff := fun f => unionComplex_continuous_iff X f
      polyhedron_isClosed_iff := unionComplex_isClosed_iff X
      polyhedralColimitHomeomorph := polyhedralColimitHomeomorph X
      polyhedralColimitHomeomorph_leg := polyhedralColimitHomeomorph_leg X
      polyhedralColimitHomeomorph_inverse_leg := polyhedralColimitHomeomorph_inverse_leg X
      polyhedralStageCellLabels := actualStageCanonicalCellEmbedding X
      polyhedralStageCell_characteristicDiskMap := by
        intro n m a
        apply ConcreteCategory.hom_ext
        intro q
        simpa only [TopCat.comp_app, characteristicDiskMap_apply] using!
          actualStageCanonicalCellEmbedding_disk X n m a q
      polyhedralStageCell_covered := actualCanonicalUnionCell_covered X
      originalEnd := (originalXToCommon X).hom
      originalEnd_closed := originalXToCommon_isClosedEmbedding X
      originalEnd_stage := fun n x => ConcreteCategory.congr_hom (originalXToCommon_stage X n) x
      originalEnd_image_stage := originalXToCommon_image_stage X
      polyhedralEnd := actualPolyhedralRealizationToCommon X
      polyhedralEnd_closed := actualPolyhedralRealizationToCommon_closed X
      polyhedralEnd_stage := actualPolyhedralRealizationToCommon_stage X
      polyhedralEnd_image_stage := actualPolyhedralRealizationToCommon_image_stage X
      global_end_intersection := actualRealization_global_end_intersection X
      initialOriginalHomeomorph := S.initialOriginalHomeomorph
      initialOriginalHomeomorph_original := S.initial_original
      initialVertices := S.initialVertices
      initialVertices_eq := rfl
      initial_original_value := by
        intro z
        have h : originalXToCommon X (skeletonInclusion X 1 z) =
            commonStageInclusion X 0 ((S.stages 0).original z) :=
          ConcreteCategory.congr_hom (originalXToCommon_stage X 0) z
        have hi : (S.stages 0).original z = S.initialOriginalHomeomorph z :=
          ContinuousMap.congr_fun S.initial_original z
        exact h.trans (congrArg (commonStageInclusion X 0) hi)
      global_zero_intersection := by
        have hr : Set.range (commonStageInclusion X 0) =
            Set.range (fun z : skeletonTop X 1 =>
              originalXToCommon X (skeletonInclusion X 1 z)) := by
          ext y
          constructor
          · rintro ⟨a, rfl⟩
            let z := S.initialOriginalHomeomorph.symm a
            have h : originalXToCommon X (skeletonInclusion X 1 z) =
                commonStageInclusion X 0 ((S.stages 0).original z) :=
              ConcreteCategory.congr_hom (originalXToCommon_stage X 0) z
            have hi : (S.stages 0).original z = a :=
              (ContinuousMap.congr_fun S.initial_original z).trans
                (S.initialOriginalHomeomorph.apply_symm_apply a)
            exact ⟨z, h.trans (congrArg (commonStageInclusion X 0) hi)⟩
          · rintro ⟨z, rfl⟩
            have h : originalXToCommon X (skeletonInclusion X 1 z) =
                commonStageInclusion X 0 ((S.stages 0).original z) :=
              ConcreteCategory.congr_hom (originalXToCommon_stage X 0) z
            exact ⟨(S.stages 0).original z, h.symm⟩
        exact (actualRealization_global_end_intersection X).trans hr
      zeroPolyhedral := fun j => stagePolyhedralInclusion X 0 (S.zeroPolyhedral j 0)
      zeroPolyhedral_initial := fun _ => rfl
      zero_ends_value := by
        intro j
        have hp := actualPolyhedralRealizationToCommon_stage X 0 (S.zeroPolyhedral j 0)
        have hs := congrArg (commonStageInclusion X 0) (S.zero_same j 0)
        have ho := ConcreteCategory.congr_hom (originalXToCommon_stage X 0) (S.zeroOriginal j 0)
        have hz : skeletonInclusion X 1 (S.zeroOriginal j 0) = map (C := (Set.univ : Set X)) 0 j 0 :=
          S.zero_value j 0
        exact hp.trans (hs.symm.trans (ho.symm.trans (congrArg (originalXToCommon X) hz)))
      polyhedralEndLabels := canonicalEndEmbedding X
      polyhedralEndSubcomplex := canonicalPolyhedralEndSubcomplex X
      polyhedralEndSubcomplex_carrier := canonicalPolyhedralEndSubcomplex_carrier X
      polyhedralEndSubcomplex_labels := canonicalPolyhedralEndSubcomplex_labels X
      polyhedralEnd_characteristicDiskMap := canonicalEndEmbedding_characteristicDiskMap X
      polyhedralEndLabels_stage := canonicalEndEmbedding_stage X
      polyhedralEndSubcomplex_stage_image := canonicalPolyhedralEndSubcomplex_stage_image X }

end Topology.CWComplex
end
