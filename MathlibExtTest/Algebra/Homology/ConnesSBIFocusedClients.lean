/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.ConnesSBI
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Ring.Rat
import Mathlib.LinearAlgebra.Prod

/-!
# Focused clients of chain-level Connes SBI presentations

A concrete split short exact `ConnesSBIPresentation` in `ModuleCat ℚ`. Write `V = ℚ²`, `L = ℚ`
and `snd : V → L` for the second projection.

* The middle complex `T` is `V ← L ← V ← L ← ⋯`, periodic of period two: `d₂₁ = snd`,
  `d₁₀ = 0`, and `d (n + 3) (n + 2) = d (n + 1) n`. Its homology is `V` in degree zero, zero in
  odd degrees and `ker snd ≅ ℚ` in even degrees `≥ 2`.
* The first complex `O` is `V` in degree zero, `L` in degree one and zero above, with zero
  differentials. It is also the preferred ordinary model, compared by the identity.
* The third complex `Q` is the restriction to degrees `≥ 0` of the zero extension of `T` to
  degrees `≥ 2`, so `Q` is zero in degrees `0, 1` and agrees with `T` two degrees lower above.
  The even translation `tailIso` is the reconstruction isomorphism of that restriction.
* The inclusion `O → T` is the identity in degrees `0, 1`; the projection `T → Q` is the identity
  in degrees `≥ 2`. Each degree is split.

The derived diagram has `I 0` an isomorphism out of `H₀ = ℚ²`, `B 0 : HC 0 → H₁` an epimorphism
onto the nonzero `H₁ = ℚ`, and `S 0 : HC 2 → HC 0` a monomorphism, nonzero on the class of the
cycle `(1, 0)`. In particular `S 0 ≫ B 0 = 0` and `exact_SB 0` hold at a position where both maps
are nonzero. The file also checks the connective boundary (`I 0` iso, `I 1` epi, `HC 1 = 0` while
`H 1 ≠ 0`) and runs the comparison theorems and `toSBIHom` on the negation endomorphism of the
presentation.
-/

open CategoryTheory Limits

namespace MathlibExtTest.Algebra.Homology.ConnesSBIFocusedClients

/-- `ℚ²`. -/
abbrev V : ModuleCat ℚ := ModuleCat.of ℚ (ℚ × ℚ)

/-- `ℚ`. -/
abbrev L : ModuleCat ℚ := ModuleCat.of ℚ ℚ

/-- The zero module. -/
abbrev Z : ModuleCat ℚ := ModuleCat.of ℚ PUnit

theorem Z_isZero : IsZero Z := ModuleCat.isZero_of_subsingleton Z

/-- `(a, b) ↦ b`. -/
abbrev sndL : V ⟶ L := ModuleCat.ofHom (LinearMap.snd ℚ ℚ ℚ)

/-- `t ↦ (t, 0)`. -/
abbrev inlL : L ⟶ V := ModuleCat.ofHom (LinearMap.inl ℚ ℚ ℚ)

/-- `t ↦ (0, t)`. -/
abbrev inrL : L ⟶ V := ModuleCat.ofHom (LinearMap.inr ℚ ℚ ℚ)

theorem inlL_sndL : inlL ≫ sndL = 0 := ModuleCat.hom_ext (LinearMap.ext fun t => by simp)

theorem inrL_sndL : inrL ≫ sndL = 𝟙 L := ModuleCat.hom_ext (LinearMap.ext fun t => by simp)

theorem inlL_ne_zero : inlL ≠ 0 := by
  intro h
  have h₁ := congrArg (fun f : L ⟶ V => f.hom (1 : ℚ)) h
  simp at h₁

theorem id_L_ne_zero : 𝟙 L ≠ 0 := by
  intro h
  have h₁ := congrArg (fun f : L ⟶ L => f.hom (1 : ℚ)) h
  simp at h₁

theorem id_V_ne_zero : 𝟙 V ≠ 0 := by
  intro h
  have h₁ := congrArg (fun f : V ⟶ V => f.hom ((1 : ℚ), (0 : ℚ))) h
  simp at h₁

/-! ### The three complexes -/

/-- Terms of the periodic middle complex. -/
def perX : ℕ → ModuleCat ℚ
  | 0 => V
  | 1 => L
  | n + 2 => perX n

/-- Differentials of the periodic middle complex. -/
def perD : ∀ n : ℕ, perX (n + 1) ⟶ perX n
  | 0 => 0
  | 1 => sndL
  | n + 2 => perD n

theorem perD_comp : ∀ n : ℕ, perD (n + 1) ≫ perD n = 0
  | 0 => Limits.comp_zero
  | 1 => Limits.zero_comp
  | n + 2 => perD_comp n

/-- The middle complex. -/
noncomputable abbrev T : ChainComplex (ModuleCat ℚ) ℕ := ChainComplex.of perX perD perD_comp

theorem T_d (n : ℕ) : T.d (n + 1) n = perD n := ChainComplex.of_d perX perD n

/-- Terms of the first complex. -/
def ordX : ℕ → ModuleCat ℚ
  | 0 => V
  | 1 => L
  | _ + 2 => Z

/-- The first complex, with zero differentials. -/
noncomputable abbrev O : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of ordX (fun _ => 0) (fun _ => Limits.comp_zero)

theorem O_d (n : ℕ) : O.d (n + 1) n = 0 := ChainComplex.of_d ordX (fun _ => 0) n

/-- The zero extension of `T` to integer degrees `≥ 2`. -/
noncomputable abbrev Tz : ChainComplex (ModuleCat ℚ) ℤ :=
  T.extend (ComplexShape.embeddingDownNatToIntShift 2)

theorem Tz_isZero_lt (z : ℤ) (hz : z < 2) : IsZero (Tz.X z) :=
  HomologicalComplex.isZero_extendDownNatToIntShift_X_lt T 2 z hz

/-- The third complex: `Tz` read in degrees `≥ 0`. -/
noncomputable abbrev Q : ChainComplex (ModuleCat ℚ) ℕ :=
  Tz.restriction (ComplexShape.embeddingDownNatToIntShift 0)

theorem shift_eq (m : ℕ) :
    (ComplexShape.embeddingDownNatToIntShift 2).f m =
      (ComplexShape.embeddingDownNatToIntShift 0).f (m + 2) := by
  simp only [ComplexShape.embeddingDownNatToIntShift_f]
  push_cast
  omega

/-- The identification of `Q` with `T` two degrees lower. -/
noncomputable def qIso (m : ℕ) : Q.X (m + 2) ≅ T.X m := T.extendXIso _ (shift_eq m)

/-- Components of the inclusion `O → T`. -/
def incX : ∀ n : ℕ, ordX n ⟶ perX n
  | 0 => 𝟙 V
  | 1 => 𝟙 L
  | _ + 2 => 0

/-- The inclusion `O → T`. -/
noncomputable def inc : O ⟶ T :=
  ChainComplex.ofHom (X := O) (Y := T) incX (fun i => by
    rw [O_d, T_d, Limits.zero_comp]
    rcases i with _ | _ | i
    · exact Limits.comp_zero
    · exact Limits.zero_comp
    · exact Limits.zero_comp)

/-- Components of the projection `T → Q`. -/
noncomputable def projX : ∀ n : ℕ, T.X n ⟶ Q.X n
  | 0 => 0
  | 1 => 0
  | m + 2 => (qIso m).inv

/-- The projection `T → Q`. -/
noncomputable def proj : T ⟶ Q where
  f := projX
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rcases j with _ | _ | m
    · exact (Limits.zero_comp).trans (Limits.comp_zero).symm
    · exact (Tz_isZero_lt _ (by simp)).eq_of_tgt _ _
    · show (qIso (m + 1)).inv ≫ Tz.d ((ComplexShape.embeddingDownNatToIntShift 0).f (m + 1 + 2))
          ((ComplexShape.embeddingDownNatToIntShift 0).f (m + 2)) =
        T.d (m + 1 + 2) (m + 2) ≫ (qIso m).inv
      rw [T.extend_d_eq _ (shift_eq (m + 1)) (shift_eq m)]
      unfold qIso
      rw [Iso.inv_hom_id_assoc, T_d m]
      erw [T_d (m + 2)]
      rfl

/-- The short complex `O → T → Q`. -/
noncomputable def sc : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) where
  f := inc
  g := proj
  zero := by
    ext n : 1
    rcases n with _ | _ | m
    · exact Limits.comp_zero
    · exact Limits.comp_zero
    · exact Limits.zero_comp

theorem sc_shortExact : sc.ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  rcases i with _ | _ | m
  · exact ShortComplex.Splitting.shortExact
      { r := 𝟙 V
        s := 0
        f_r := Category.comp_id _
        s_g := (Tz_isZero_lt _ (by simp)).eq_of_src _ _
        id := by
          rw [Limits.comp_zero, add_zero]
          exact Category.id_comp _ }
  · exact ShortComplex.Splitting.shortExact
      { r := 𝟙 L
        s := 0
        f_r := Category.comp_id _
        s_g := (Tz_isZero_lt _ (by simp)).eq_of_src _ _
        id := by
          rw [Limits.comp_zero, add_zero]
          exact Category.id_comp _ }
  · exact ShortComplex.Splitting.shortExact
      { r := 0
        s := (qIso m).hom
        f_r := Z_isZero.eq_of_src _ _
        s_g := (qIso m).hom_inv_id
        id := by
          rw [Limits.zero_comp, zero_add]
          exact (qIso m).inv_hom_id }

/-- The presentation. -/
noncomputable def D : ConnesSBIPresentation (A := ModuleCat ℚ) where
  ordinary := O
  shortComplex := sc
  shortExact := sc_shortExact
  ordinaryComparison := 𝟙 O
  ordinaryComparisonQuasiIso := quasiIso_of_isIso (𝟙 O)
  tailIso := HomologicalComplex.restrictExtendDownNatToIntShiftIso Tz 0
    (fun i hi => Tz_isZero_lt i (by omega))

/-! ### Homology of the model -/

/-- A nonzero cycle in a degree whose incoming differential vanishes has a nonzero class. -/
theorem homology_ne_zero (K : ChainComplex (ModuleCat ℚ) ℕ) (i j : ℕ)
    (hj : (ComplexShape.down ℕ).next i = j) (hin : K.d (i + 1) i = 0) {A : ModuleCat ℚ}
    (x : A ⟶ K.X i) (hx : x ≫ K.d i j = 0) (hx0 : x ≠ 0) : ¬ IsZero (K.homology i) := by
  intro hZ
  have : IsIso (K.homologyπ i) := K.isIso_homologyπ (i + 1) i (by simp) hin
  apply hx0
  have h₁ : K.liftCycles x j hj hx ≫ K.homologyπ i = 0 ≫ K.homologyπ i :=
    hZ.eq_of_tgt _ _
  rw [← K.liftCycles_i x j hj hx, (cancel_mono (K.homologyπ i)).1 h₁, Limits.zero_comp]

theorem O_homology_zero_ne_zero : ¬ IsZero (O.homology 0) :=
  homology_ne_zero O 0 0 (by simp) (O_d 0) (𝟙 V)
    (by rw [O.shape 0 0 (by simp)]; exact Limits.comp_zero) id_V_ne_zero

theorem O_homology_one_ne_zero : ¬ IsZero (O.homology 1) :=
  homology_ne_zero O 1 0 (by simp) (O_d 1) (𝟙 L) (by rw [O_d 0]; exact Limits.comp_zero)
    id_L_ne_zero

theorem O_homology_two_isZero : IsZero (O.homology 2) :=
  (O.sc 2).isZero_homology_of_isZero_X₂ Z_isZero

theorem T_d_two_one : T.d 2 1 = sndL := T_d 1

theorem inlL_comp_T_d : inlL ≫ T.d 2 1 = 0 := by
  rw [T_d_two_one]
  exact inlL_sndL

/-- `HC 2 = H₂(T)` contains the class of `(1, 0) ∈ ker snd`. -/
theorem T_homology_two_ne_zero : ¬ IsZero (T.homology 2) :=
  homology_ne_zero T 2 1 (by simp) (T_d 2) inlL inlL_comp_T_d inlL_ne_zero

/-- `HC 1 = H₁(T)` vanishes: `snd` is onto. -/
theorem T_homology_one_isZero : IsZero (T.homology 1) := by
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [T.exactAt_iff' 2 1 0 (by simp) (by simp)]
  refine (ShortComplex.exact_iff_epi _ (T_d 0)).2 ?_
  change Epi (T.d 2 1)
  rw [T_d_two_one]
  exact (epi_of_epi_fac inrL_sndL : Epi sndL)

/-! ### The derived SBI diagram -/

theorem zero_ne_of_isIso {X Y : ModuleCat ℚ} (hX : ¬ IsZero X) (f : X ⟶ Y) (hf : IsIso f) :
    f ≠ 0 := by
  intro h
  subst h
  apply hX
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : X ⟶ Y), Limits.zero_comp]

theorem ne_zero_of_epi {X Y : ModuleCat ℚ} (hY : ¬ IsZero Y) (f : X ⟶ Y) (hf : Epi f) :
    f ≠ 0 := by
  intro h
  apply hY
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_epi f).1 (by rw [h, Limits.zero_comp, Limits.zero_comp])

theorem ne_zero_of_mono {X Y : ModuleCat ℚ} (hX : ¬ IsZero X) (f : X ⟶ Y) (hf : Mono f) :
    f ≠ 0 := by
  intro h
  apply hX
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_mono f).1 (by rw [h, Limits.comp_zero, Limits.comp_zero])

/-- Boundary: `I 0` is an isomorphism out of the nonzero `H₀ = ℚ²`. -/
theorem I_zero_iso_ne_zero : IsIso (D.I 0) ∧ D.I 0 ≠ 0 := by
  exact ⟨D.isIso_I_zero, zero_ne_of_isIso O_homology_zero_ne_zero (D.I 0) D.isIso_I_zero⟩

/-- Boundary: `I 1` is an epimorphism onto `HC 1 = 0`, from the nonzero `H₁ = ℚ`. -/
theorem I_one_boundary :
    Epi (D.I 1) ∧ D.I 1 = 0 ∧ IsZero (D.HC 1) ∧ ¬ IsZero (D.ordinary.homology 1) :=
  ⟨D.epi_I_one, T_homology_one_isZero.eq_of_tgt _ _, T_homology_one_isZero,
    O_homology_one_ne_zero⟩

/-- The tail homology vanishes below degree two. -/
theorem tail_low : IsZero (D.shortComplex.X₃.homology 0) ∧ IsZero (D.shortComplex.X₃.homology 1) :=
  ⟨D.isZero_tailHomology_of_lt_two 0 (by omega), D.isZero_tailHomology_of_lt_two 1 (by omega)⟩

/-- `B 0 : HC 0 → H₁ = ℚ` is an epimorphism, hence nonzero. -/
theorem B_zero_epi : Epi (D.B 0) :=
  (ShortComplex.exact_iff_epi _ (T_homology_one_isZero.eq_of_tgt _ _)).1 (D.exact_BI 0)

theorem B_zero_ne_zero : D.B 0 ≠ 0 :=
  ne_zero_of_epi O_homology_one_ne_zero (D.B 0) B_zero_epi

/-- `S 0 : HC 2 → HC 0` is a monomorphism out of the nonzero `HC 2`, hence nonzero. -/
theorem S_zero_mono : Mono (D.S 0) :=
  (ShortComplex.exact_iff_mono _ (O_homology_two_isZero.eq_of_src _ _)).1 (D.exact_IS 0)

theorem S_zero_ne_zero : D.S 0 ≠ 0 :=
  ne_zero_of_mono T_homology_two_ne_zero (D.S 0) S_zero_mono

/-- The class of the cycle `(1, 0)` in `HC 2`. -/
noncomputable def classTwo : L ⟶ D.HC 2 :=
  T.liftCycles (i := 2) inlL 1 (by simp) inlL_comp_T_d ≫ T.homologyπ 2

/-- `S 0` is nonzero on the class of `(1, 0)`. -/
theorem S_zero_on_classTwo : classTwo ≫ D.S 0 ≠ 0 := by
  have := S_zero_mono
  intro h
  have h₁ : classTwo = 0 := (cancel_mono (D.S 0)).1 (h.trans (Limits.zero_comp).symm)
  have : IsIso (T.homologyπ 2) := T.isIso_homologyπ 3 2 (by simp) (T_d 2)
  apply inlL_ne_zero
  rw [← T.liftCycles_i (i := 2) inlL 1 (by simp) inlL_comp_T_d,
    (cancel_mono (T.homologyπ 2)).1 (h₁.trans (Limits.zero_comp).symm), Limits.zero_comp]
  rfl

/-- At `HC 0` both maps are nonzero, their composite vanishes, and the pair is exact. -/
theorem SB_zero :
    D.S 0 ≫ D.B 0 = 0 ∧ D.S 0 ≠ 0 ∧ D.B 0 ≠ 0 ∧
      (ShortComplex.mk (D.S 0) (D.B 0) (D.S_comp_B 0)).Exact :=
  ⟨D.S_comp_B 0, S_zero_ne_zero, B_zero_ne_zero, D.exact_SB 0⟩

/-- The derived diagram is an exact connective SBI diagram. -/
theorem sbi_exact_connective : D.sbiDiagram.Exact ∧ D.sbiDiagram.ConnectiveBoundary :=
  ⟨D.sbiDiagram_exact, D.sbiDiagram_connectiveBoundary⟩

/-! ### A comparison morphism -/

theorem extendMap_neg {K K' : ChainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ K') (b : ℤ) :
    HomologicalComplex.extendMap (-φ) (ComplexShape.embeddingDownNatToIntShift b) =
      -HomologicalComplex.extendMap φ (ComplexShape.embeddingDownNatToIntShift b) :=
  eq_neg_of_add_eq_zero_left (by
    rw [← HomologicalComplex.extendMap_add, neg_add_cancel, HomologicalComplex.extendMap_zero])

/-- Negation of the whole presentation. -/
noncomputable def negHom : D ⟶ D where
  ordinaryMap := -𝟙 _
  shortMap := -𝟙 _
  ordinaryComparison_naturality := by simp
  tailIso_naturality := by
    simp only [ShortComplex.neg_τ₃, ShortComplex.neg_τ₂, ShortComplex.id_τ₃, ShortComplex.id_τ₂,
      extendMap_neg, HomologicalComplex.extendMap_id, Preadditive.neg_comp, Preadditive.comp_neg,
      Category.id_comp, Category.comp_id]

instance negId_isIso {C : Type*} [Category C] [Preadditive C] (X : C) : IsIso (-𝟙 X) :=
  ⟨⟨-𝟙 X, by simp, by simp⟩⟩

theorem negHom_hMap (n : ℕ) : negHom.hMap n = -𝟙 _ := by
  simp [ConnesSBIPresentation.Hom.hMap, negHom]

theorem negHom_hcMap (n : ℕ) : negHom.hcMap n = -𝟙 _ := by
  simp [ConnesSBIPresentation.Hom.hcMap, negHom]

/-- The comparison theorem applied to `negHom`. -/
theorem negHom_isIso_hcMap (n : ℕ) : IsIso (negHom.hcMap n) :=
  negHom.isIso_hcMap_of_isIso_hMap (fun m => by rw [negHom_hMap]; infer_instance) n

/-- `toSBIHom` sends `negHom` to negation on cyclic-type homology. -/
theorem toSBIHom_negHom_hcMap (n : ℕ) : negHom.toSBIHom.hcMap n = -𝟙 (D.HC n) :=
  negHom_hcMap n

/-- The chain-level comparison: `negHom` is a quasi-isomorphism on the middle complexes. -/
theorem negHom_quasiIso : QuasiIso negHom.shortMap.τ₂ := by
  have : QuasiIso negHom.ordinaryMap := by
    change QuasiIso (-𝟙 O)
    exact quasiIso_of_isIso _
  exact negHom.quasiIso_shortMap_τ₂

end MathlibExtTest.Algebra.Homology.ConnesSBIFocusedClients
