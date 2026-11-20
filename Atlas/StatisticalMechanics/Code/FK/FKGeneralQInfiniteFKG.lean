/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.FKGeneralQConsumer
import Code.FK.FKG
import Code.Probability.InfiniteHarris










open MeasureTheory Filter Topology SimpleGraph
open StatMech.Lattice StatMech.IsingFK

namespace StatMech.FK

variable {d : Nat}



theorem fkgq_freeFiniteMeasure_fkg
    (N m : Nat) (hNm : N <= m) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' S₁) *
        (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' S₂) <=
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  let T₁ := boxRestrictLE d hNm ⁻¹' S₁
  let T₂ := boxRestrictLE d hNm ⁻¹' S₂
  have hT₁inc : IsIncreasing T₁ := fun a b hab ha =>
    hS₁ (boxRestrictLE_monotone d hNm hab) ha
  have hT₂inc : IsIncreasing T₂ := fun a b hab ha =>
    hS₂ (boxRestrictLE_monotone d hNm hab) ha
  have heq₁ : boxRestrict d N ⁻¹' S₁ = boxRestrict d m ⁻¹' T₁ := by
    ext omega
    simp only [T₁, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have heq₂ : boxRestrict d N ⁻¹' S₂ = boxRestrict d m ⁻¹' T₂ := by
    ext omega
    simp only [T₂, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas₁ : MeasurableSet (boxRestrict d m ⁻¹' T₁) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeas₂ : MeasurableSet (boxRestrict d m ⁻¹' T₂) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeascap : MeasurableSet (boxRestrict d m ⁻¹' (T₁ ∩ T₂)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq₁, heq₂, <- Set.preimage_inter,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) T₁ hmeas₁,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) T₂ hmeas₂,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) (T₁ ∩ T₂) hmeascap]
  have hfkg := fkProb_positively_associated_events (boxGraph d m) hp hp1 hq
    hT₁inc hT₂inc
  calc
    (∑ omega, T₁.indicator (fun _ => (1 : Real)) omega *
          fkProb (boxGraph d m) p q omega) *
        (∑ omega, T₂.indicator (fun _ => (1 : Real)) omega *
          fkProb (boxGraph d m) p q omega) =
      (∑ omega, fkProb (boxGraph d m) p q omega *
          T₁.indicator (fun _ => (1 : Real)) omega) *
        (∑ omega, fkProb (boxGraph d m) p q omega *
          T₂.indicator (fun _ => (1 : Real)) omega) := by
            rw [Finset.sum_congr rfl
                (fun omega _ => mul_comm (T₁.indicator _ omega) _),
              Finset.sum_congr rfl
                (fun omega _ => mul_comm (T₂.indicator _ omega) _)]
    _ <= ∑ omega, fkProb (boxGraph d m) p q omega *
        (T₁ ∩ T₂).indicator (fun _ => (1 : Real)) omega := hfkg
    _ = ∑ omega, (T₁ ∩ T₂).indicator (fun _ => (1 : Real)) omega *
        fkProb (boxGraph d m) p q omega :=
      Finset.sum_congr rfl (fun omega _ => mul_comm _ _)



theorem fkgq_freeInfiniteVolume_fkg
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS₁ : IsIncreasing S₁) (hS₂ : IsIncreasing S₂) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' S₁) *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' S₂) <=
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
  have hlim₁ := fkgq_free_infinite_measure N hp hp1 hq hS₁
  have hlim₂ := fkgq_free_infinite_measure N hp hp1 hq hS₂
  have hlimcap := fkgq_free_infinite_measure N hp hp1 hq (hS₁.inter hS₂)
  have hlimcap' : Tendsto
      (fun m => (freeFiniteMeasure d m hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂)) atTop
      (nhds ((freeInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂))) := by
    simpa only [Set.preimage_inter] using hlimcap
  apply le_of_tendsto_of_tendsto (hlim₁.mul hlim₂) hlimcap'
  filter_upwards [eventually_ge_atTop N] with m hm
  exact fkgq_freeFiniteMeasure_fkg N m hm hp hp1 hq hS₁ hS₂




theorem fkgq_freeInfiniteVolume_fkg_of_dependsOn
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A B : Set (ConfigSpace (Sym2 (Site d)))}
    (hAdep : StatMech.DependsOn A (Set.range (edgeIncl d N)))
    (hBdep : StatMech.DependsOn B (Set.range (edgeIncl d N)))
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real A *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real B <=
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (A ∩ B) := by
  let S₁ : Set (ConfigSpace (Sym2 (boxVerts d N))) := extendEdge d N ⁻¹' A
  let S₂ : Set (ConfigSpace (Sym2 (boxVerts d N))) := extendEdge d N ⁻¹' B
  have hS₁ : IsIncreasing S₁ := fun a b hab ha =>
    hA (monotone_extendEdge d N hab) ha
  have hS₂ : IsIncreasing S₂ := fun a b hab ha =>
    hB (monotone_extendEdge d N hab) ha
  have hrestrict_extend (omega : ConfigSpace (Sym2 (Site d))) :
      ∀ e ∈ Set.range (edgeIncl d N),
        omega e = extendEdge d N (boxRestrict d N omega) e := by
    rintro _ ⟨eb, rfl⟩
    rw [extendEdge_eq_of_range]
    rfl
  have heq₁ : A = boxRestrict d N ⁻¹' S₁ := by
    ext omega
    apply hAdep omega (extendEdge d N (boxRestrict d N omega))
    intro e he
    exact (hrestrict_extend omega e he).symm
  have heq₂ : B = boxRestrict d N ⁻¹' S₂ := by
    ext omega
    apply hBdep omega (extendEdge d N (boxRestrict d N omega))
    intro e he
    exact (hrestrict_extend omega e he).symm
  rw [heq₁, heq₂]
  exact fkgq_freeInfiniteVolume_fkg N hp hp1 hq hS₁ hS₂



theorem fkgq_freeInfiniteVolume_fkg_iInter
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (N : Nat -> Nat)
    (S₁ S₂ : (n : Nat) -> Set (ConfigSpace (Sym2 (boxVerts d (N n)))))
    (hS₁ : forall n, IsIncreasing (S₁ n))
    (hS₂ : forall n, IsIncreasing (S₂ n))
    (hanti₁ : Antitone (fun n => boxRestrict d (N n) ⁻¹' S₁ n))
    (hanti₂ : Antitone (fun n => boxRestrict d (N n) ⁻¹' S₂ n)) :
    let mu := (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))
    mu.real (⋂ n, boxRestrict d (N n) ⁻¹' S₁ n) *
        mu.real (⋂ n, boxRestrict d (N n) ⁻¹' S₂ n) <=
      mu.real ((⋂ n, boxRestrict d (N n) ⁻¹' S₁ n) ∩
        (⋂ n, boxRestrict d (N n) ⁻¹' S₂ n)) := by
  let mu := (freeInfiniteVolume d hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))
  apply StatMech.ih_harris_iInter_of_antitone mu
    (fun n => boxRestrict d (N n) ⁻¹' S₁ n)
    (fun n => boxRestrict d (N n) ⁻¹' S₂ n) hanti₁ hanti₂
  · intro n
    exact (continuous_boxRestrict d (N n)).measurable MeasurableSet.of_discrete
  · intro n
    exact (continuous_boxRestrict d (N n)).measurable MeasurableSet.of_discrete
  · intro n
    exact fkgq_freeInfiniteVolume_fkg (N n) hp hp1 hq (hS₁ n) (hS₂ n)




theorem fkgq_freeInfiniteVolume_fkg_iInter_of_dependsOn
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (N : Nat -> Nat)
    (A B : Nat -> Set (ConfigSpace (Sym2 (Site d))))
    (hAdep : forall n,
      StatMech.DependsOn (A n) (Set.range (edgeIncl d (N n))))
    (hBdep : forall n,
      StatMech.DependsOn (B n) (Set.range (edgeIncl d (N n))))
    (hA : forall n, IsIncreasing (A n))
    (hB : forall n, IsIncreasing (B n))
    (hAmeas : forall n, MeasurableSet (A n))
    (hBmeas : forall n, MeasurableSet (B n))
    (hantiA : Antitone A) (hantiB : Antitone B) :
    let mu := (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))
    mu.real (⋂ n, A n) * mu.real (⋂ n, B n) <=
      mu.real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
  let mu := (freeInfiniteVolume d hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))
  apply StatMech.ih_harris_iInter_of_antitone mu A B hantiA hantiB
    hAmeas hBmeas
  intro n
  exact fkgq_freeInfiniteVolume_fkg_of_dependsOn (N n) hp hp1 hq
    (hAdep n) (hBdep n) (hA n) (hB n)

end StatMech.FK
