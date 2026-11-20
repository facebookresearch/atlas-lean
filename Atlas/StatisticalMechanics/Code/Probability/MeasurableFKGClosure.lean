/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.FreeDLRExtreme
import Code.Probability.InfiniteHarris
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Profinite









open Filter MeasureTheory Set Topology

namespace StatMech

variable {E : Type*} [DecidableEq E] [Countable E]

theorem isClopen_of_dependsOn_finset
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : DependsOn A (F : Set E)) : IsClopen A := by
  rw [ih_eq_cylinder_of_dependsOn F hA]
  exact isClopen_cylinderEvent F _


def finiteUpwardHull (F : Finset E) (A : Set (ConfigSpace E)) :
    Set (ConfigSpace E) :=
  {eta | ∃ omega ∈ A, ∀ e ∈ F, omega e ≤ eta e}

theorem finiteUpwardHull_dependsOn
    (F : Finset E) (A : Set (ConfigSpace E)) :
    DependsOn (finiteUpwardHull F A) (F : Set E) := by
  intro eta theta hagree
  constructor
  · rintro ⟨omega, homega, hle⟩
    exact ⟨omega, homega, fun e he => by
      rw [hagree e he]
      exact hle e he⟩
  · rintro ⟨omega, homega, hle⟩
    exact ⟨omega, homega, fun e he => by
      rw [← hagree e he]
      exact hle e he⟩

theorem finiteUpwardHull_isClopen
    (F : Finset E) (A : Set (ConfigSpace E)) :
    IsClopen (finiteUpwardHull F A) :=
  isClopen_of_dependsOn_finset _ F (finiteUpwardHull_dependsOn F A)

theorem finiteUpwardHull_isIncreasing
    (F : Finset E) (A : Set (ConfigSpace E)) :
    IsIncreasing (finiteUpwardHull F A) := by
  intro eta theta heta hmem
  obtain ⟨omega, homega, hle⟩ := hmem
  exact ⟨omega, homega, fun e he => (hle e he).trans (heta e)⟩

theorem subset_finiteUpwardHull
    (F : Finset E) (A : Set (ConfigSpace E)) :
    A ⊆ finiteUpwardHull F A := by
  intro omega homega
  exact ⟨omega, homega, fun _ _ => le_rfl⟩

theorem isClosed_Iic_config (x : ConfigSpace E) :
    IsClosed (Set.Iic x) := by
  have heq : Set.Iic x = ⋂ e : E, (fun omega : ConfigSpace E => omega e) ⁻¹'
      {b : Bool | b ≤ x e} := by
    ext omega
    simp only [Set.mem_Iic, Set.mem_iInter, Set.mem_preimage,
      Set.mem_setOf_eq, Pi.le_def]
  rw [heq]
  exact isClosed_iInter fun e =>
    (isClosed_discrete {b : Bool | b ≤ x e}).preimage (continuous_apply e)

theorem finiteUpwardHull_not_mem_of_disjoint_Iic
    (F : Finset E) (A : Set (ConfigSpace E)) (x : ConfigSpace E)
    (hA : DependsOn A (F : Set E))
    (hdisjoint : Disjoint A (Set.Iic x)) :
    x ∉ finiteUpwardHull F A := by
  rintro ⟨omega, homega, hle⟩
  let rho : ConfigSpace E := fun e => if e ∈ F then omega e else false
  have hagree : agreeOn (F : Set E) omega rho := by
    intro e he
    have heF : e ∈ F := he
    simp only [rho, if_pos heF]
  have hrhoA : rho ∈ A := (hA omega rho hagree).mp homega
  have hrhole : rho ≤ x := by
    intro e
    by_cases he : e ∈ F
    · simpa only [rho, if_pos he] using hle e he
    · simp only [rho, if_neg he]
      exact Bool.false_le _
  exact Set.disjoint_left.1 hdisjoint hrhoA hrhole



theorem exists_increasing_isClopen_superset_not_mem
    (C : Set (ConfigSpace E)) (hCclosed : IsClosed C)
    (hCinc : IsIncreasing C) {x : ConfigSpace E} (hx : x ∉ C) :
    ∃ H : Set (ConfigSpace E), IsClopen H ∧ IsIncreasing H ∧
      C ⊆ H ∧ x ∉ H := by
  have hCIic : C ⊆ (Set.Iic x)ᶜ := by
    intro omega homega hle
    exact hx (hCinc hle homega)
  obtain ⟨U, hUclopen, hCU, hUsub⟩ :=
    exists_clopen_of_closed_subset_open hCclosed
      (isClosed_Iic_config x).isOpen_compl hCIic
  obtain ⟨F, hF⟩ := FK.isClopen_dependsOn_finset U hUclopen
  refine ⟨finiteUpwardHull F U, finiteUpwardHull_isClopen F U,
    finiteUpwardHull_isIncreasing F U,
    hCU.trans (subset_finiteUpwardHull F U), ?_⟩
  apply finiteUpwardHull_not_mem_of_disjoint_Iic F U x hF
  exact Set.disjoint_left.2 fun omega homega hle => hUsub homega hle



theorem exists_antitone_isClopen_isIncreasing_iInter_eq
    (C : Set (ConfigSpace E)) (hCclosed : IsClosed C)
    (hCinc : IsIncreasing C) :
    ∃ A : Nat → Set (ConfigSpace E), Antitone A ∧
      (∀ n, IsClopen (A n)) ∧ (∀ n, IsIncreasing (A n)) ∧
      (⋂ n, A n) = C := by
  classical
  by_cases hCuniv : C = Set.univ
  · refine ⟨fun _ => Set.univ, antitone_const, fun _ => isClopen_univ,
      fun _ _ _ _ _ => Set.mem_univ _, ?_⟩
    simp only [iInter_univ, hCuniv]
  have hcompl : (Cᶜ).Nonempty := Set.nonempty_compl.mpr hCuniv
  choose H hHcl hHinc hCH hxH using fun x : (Cᶜ : Set (ConfigSpace E)) =>
    exists_increasing_isClopen_superset_not_mem C hCclosed hCinc x.2
  have hunion : ⋃ x : (Cᶜ : Set (ConfigSpace E)), (H x)ᶜ = Cᶜ := by
    apply Set.Subset.antisymm
    · intro omega homega
      obtain ⟨x, hx⟩ := Set.mem_iUnion.1 homega
      exact fun homegaC => hx (hCH x homegaC)
    · intro omega homega
      exact Set.mem_iUnion.2 ⟨⟨omega, homega⟩, hxH ⟨omega, homega⟩⟩
  obtain ⟨T, hTcount, hTunion⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : (Cᶜ : Set (ConfigSpace E)) => (H x)ᶜ)
      (fun x => (hHcl x).compl.isOpen)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hselected : (⋃ x ∈ T, (H x)ᶜ) = ∅ := by
      rw [hTempty]
      simp
    have hfull : (⋃ x : (Cᶜ : Set (ConfigSpace E)), (H x)ᶜ) = ∅ := by
      rw [← hTunion, hselected]
    exact hcompl.ne_empty (by rw [← hunion]; exact hfull)
  obtain ⟨f, hf⟩ := Set.Countable.exists_surjective hTnonempty hTcount
  let A : Nat → Set (ConfigSpace E) := fun n =>
    ⋂ i : Fin (n + 1), H (f i).1
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro n m hnm omega homega
    simp only [A, Set.mem_iInter] at homega ⊢
    intro i
    exact homega ⟨i.1, lt_of_lt_of_le i.2 (Nat.add_le_add_right hnm 1)⟩
  · intro n
    exact isClopen_iInter_of_finite fun i => hHcl (f i).1
  · intro n omega eta hle homega
    simp only [A, Set.mem_iInter] at homega ⊢
    intro i
    exact hHinc (f i).1 hle (homega i)
  · ext omega
    simp only [Set.mem_iInter]
    constructor
    · intro homega
      by_contra hnot
      have hcomp : omega ∈ Cᶜ := hnot
      have hcovered : omega ∈ ⋃ x ∈ T, (H x)ᶜ := by
        rw [hTunion, hunion]
        exact hcomp
      obtain ⟨x, hx⟩ := Set.mem_iUnion.1 hcovered
      obtain ⟨hxT, hxH'⟩ := Set.mem_iUnion.1 hx
      obtain ⟨k, hk⟩ := hf ⟨x, hxT⟩
      have hkA := homega k
      simp only [A, Set.mem_iInter] at hkA
      have hmem := hkA ⟨k, Nat.lt_succ_self k⟩
      exact hxH' (by simpa only [hk] using hmem)
    · intro homega n
      simp only [A, Set.mem_iInter]
      intro i
      exact hCH (f i).1 homega



def configUpwardClosure (K : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {eta | ∃ omega ∈ K, omega ≤ eta}

theorem configUpwardClosure_isIncreasing (K : Set (ConfigSpace E)) :
    IsIncreasing (configUpwardClosure K) := by
  intro eta theta hle
  rintro ⟨omega, homega, homegaeta⟩
  exact ⟨omega, homega, homegaeta.trans hle⟩

theorem subset_configUpwardClosure (K : Set (ConfigSpace E)) :
    K ⊆ configUpwardClosure K := by
  intro omega homega
  exact ⟨omega, homega, le_rfl⟩

theorem configUpwardClosure_subset_of_isIncreasing
    {K A : Set (ConfigSpace E)} (hKA : K ⊆ A) (hA : IsIncreasing A) :
    configUpwardClosure K ⊆ A := by
  rintro eta ⟨omega, homega, hle⟩
  exact hA hle (hKA homega)

theorem configOrder_isClosed :
    IsClosed {z : ConfigSpace E × ConfigSpace E | z.1 ≤ z.2} := by
  have heq : {z : ConfigSpace E × ConfigSpace E | z.1 ≤ z.2} =
      ⋂ e : E, (fun z : ConfigSpace E × ConfigSpace E =>
        (z.1 e, z.2 e)) ⁻¹' {b : Bool × Bool | b.1 ≤ b.2} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Pi.le_def]
  rw [heq]
  exact isClosed_iInter fun e =>
    (isClosed_discrete {b : Bool × Bool | b.1 ≤ b.2}).preimage
      (((continuous_apply e).comp continuous_fst).prodMk
        ((continuous_apply e).comp continuous_snd))

theorem configUpwardClosure_isCompact
    {K : Set (ConfigSpace E)} (hK : IsCompact K) :
    IsCompact (configUpwardClosure K) := by
  let R : Set (ConfigSpace E × ConfigSpace E) :=
    (K ×ˢ Set.univ) ∩ {z | z.1 ≤ z.2}
  have hR : IsCompact R :=
    (hK.prod isCompact_univ).inter_right configOrder_isClosed
  have himage : configUpwardClosure K = Prod.snd '' R := by
    ext eta
    constructor
    · rintro ⟨omega, homega, hle⟩
      exact ⟨(omega, eta), ⟨⟨homega, Set.mem_univ eta⟩, hle⟩, rfl⟩
    · rintro ⟨z, ⟨⟨hzK, _⟩, hzle⟩, rfl⟩
      exact ⟨z.1, hzK, hzle⟩
  rw [himage]
  exact hR.image continuous_snd

theorem configUpwardClosure_isClosed
    {K : Set (ConfigSpace E)} (hK : IsCompact K) :
    IsClosed (configUpwardClosure K) :=
  (configUpwardClosure_isCompact hK).isClosed


theorem fkg_isClosed_of_isClopen
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (hclopen : ∀ C D : Set (ConfigSpace E),
      IsClopen C → IsClopen D → IsIncreasing C → IsIncreasing D →
        mu.real C * mu.real D ≤ mu.real (C ∩ D))
    {C D : Set (ConfigSpace E)}
    (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hCinc : IsIncreasing C) (hDinc : IsIncreasing D) :
    mu.real C * mu.real D ≤ mu.real (C ∩ D) := by
  obtain ⟨A, hAanti, hAcl, hAinc, hAeq⟩ :=
    exists_antitone_isClopen_isIncreasing_iInter_eq C hCclosed hCinc
  obtain ⟨B, hBanti, hBcl, hBinc, hBeq⟩ :=
    exists_antitone_isClopen_isIncreasing_iInter_eq D hDclosed hDinc
  have hfkg := ih_harris_iInter_of_antitone mu A B hAanti hBanti
    (fun n => (hAcl n).isOpen.measurableSet)
    (fun n => (hBcl n).isOpen.measurableSet)
    (fun n => hclopen (A n) (B n) (hAcl n) (hBcl n) (hAinc n) (hBinc n))
  rwa [hAeq, hBeq] at hfkg

theorem exists_compact_subset_measureReal_lt_add
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    {A : Set (ConfigSpace E)} (hA : MeasurableSet A)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ K : Set (ConfigSpace E), K ⊆ A ∧ IsCompact K ∧
      mu.real A < mu.real K + epsilon := by
  have hepsilonENN : ENNReal.ofReal epsilon ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hepsilon).ne'
  obtain ⟨K, hKA, hK, hmeasure⟩ := hA.exists_isCompact_lt_add
    (measure_ne_top mu A) hepsilonENN
  refine ⟨K, hKA, hK, ?_⟩
  have hKtop : mu K ≠ ⊤ := measure_ne_top mu K
  have hepsTop : ENNReal.ofReal epsilon ≠ ⊤ := ENNReal.ofReal_ne_top
  have haddTop : mu K + ENNReal.ofReal epsilon ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hKtop, hepsTop⟩
  have hreal := (ENNReal.toReal_lt_toReal (measure_ne_top mu A) haddTop).mpr hmeasure
  rw [ENNReal.toReal_add hKtop hepsTop,
    ENNReal.toReal_ofReal hepsilon.le] at hreal
  simpa only [measureReal_def] using hreal



theorem fkg_measurable_of_isClopen
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (hclopen : ∀ C D : Set (ConfigSpace E),
      IsClopen C → IsClopen D → IsIncreasing C → IsIncreasing D →
        mu.real C * mu.real D ≤ mu.real (C ∩ D))
    (A B : Set (ConfigSpace E))
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) :
    mu.real A * mu.real B ≤ mu.real (A ∩ B) := by
  by_contra hnot
  have hstrict : mu.real (A ∩ B) < mu.real A * mu.real B :=
    lt_of_not_ge hnot
  let gap : Real := mu.real A * mu.real B - mu.real (A ∩ B)
  have hgap : 0 < gap := sub_pos.mpr hstrict
  let epsilon : Real := gap / 3
  have hepsilon : 0 < epsilon := div_pos hgap (by norm_num)
  obtain ⟨K, hKA, hKcompact, hKapprox⟩ :=
    exists_compact_subset_measureReal_lt_add mu hAmeas hepsilon
  obtain ⟨L, hLB, hLcompact, hLapprox⟩ :=
    exists_compact_subset_measureReal_lt_add mu hBmeas hepsilon
  let C := configUpwardClosure K
  let D := configUpwardClosure L
  have hCsub : C ⊆ A :=
    configUpwardClosure_subset_of_isIncreasing hKA hAinc
  have hDsub : D ⊆ B :=
    configUpwardClosure_subset_of_isIncreasing hLB hBinc
  have hKsubC : K ⊆ C := subset_configUpwardClosure K
  have hLsubD : L ⊆ D := subset_configUpwardClosure L
  have hclosedFKG : mu.real C * mu.real D ≤ mu.real (C ∩ D) :=
    fkg_isClosed_of_isClopen mu hclopen
      (configUpwardClosure_isClosed hKcompact)
      (configUpwardClosure_isClosed hLcompact)
      (configUpwardClosure_isIncreasing K)
      (configUpwardClosure_isIncreasing L)
  have hKL : mu.real K * mu.real L ≤ mu.real (A ∩ B) := by
    calc
      mu.real K * mu.real L ≤ mu.real C * mu.real D :=
        mul_le_mul (measureReal_mono hKsubC) (measureReal_mono hLsubD)
          measureReal_nonneg measureReal_nonneg
      _ ≤ mu.real (C ∩ D) := hclosedFKG
      _ ≤ mu.real (A ∩ B) :=
        measureReal_mono (Set.inter_subset_inter hCsub hDsub)
  have hKAmeasure : mu.real K ≤ mu.real A := measureReal_mono hKA
  have hLBmeasure : mu.real L ≤ mu.real B := measureReal_mono hLB
  have hAone : mu.real A ≤ 1 := measureReal_le_one
  have hLone : mu.real L ≤ 1 := measureReal_le_one
  have hA0 : 0 ≤ mu.real A := measureReal_nonneg
  have hL0 : 0 ≤ mu.real L := measureReal_nonneg
  have hAdiff : 0 ≤ mu.real A - mu.real K := sub_nonneg.mpr hKAmeasure
  have hBdiff : 0 ≤ mu.real B - mu.real L := sub_nonneg.mpr hLBmeasure
  have hAdiffE : mu.real A - mu.real K < epsilon := by linarith
  have hBdiffE : mu.real B - mu.real L < epsilon := by linarith
  have hfirst : mu.real A * (mu.real B - mu.real L) < epsilon := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hAone) hBdiff
    nlinarith
  have hsecond : mu.real L * (mu.real A - mu.real K) < epsilon := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hLone) hAdiff
    nlinarith
  have hproduct : mu.real A * mu.real B - mu.real K * mu.real L <
      2 * epsilon := by
    calc
      mu.real A * mu.real B - mu.real K * mu.real L =
          mu.real A * (mu.real B - mu.real L) +
            mu.real L * (mu.real A - mu.real K) := by ring
      _ < 2 * epsilon := by linarith
  dsimp only [epsilon, gap] at hproduct
  nlinarith

end StatMech
