/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from
`Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean`,
`Definitions/Def_AutomorphicForm_ArchDerivCasimirComplex.lean`,
`Theorems/Thm_AutomorphicForm_flowChart_add_single_eq_mul_conj.lean`
and
`P2M/Sol/S_AutomorphicForm_flowChart_add_single_eq_mul_conj.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import MathlibExt.NumberTheory.AutomorphicForm.ConstantTerm
public import MathlibExt.NumberTheory.AutomorphicForm.FnTwist

import Mathlib.Tactic.Group

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K]

/-- **Real archimedean flow directions.** The three directions of the real archimedean flows:
the split torus `H`, the upper unipotent `E` and the lower unipotent `Fm`. -/
inductive ArchDir where
  | H : ArchDir
  | E : ArchDir
  | Fm : ArchDir

/-- **Complex archimedean flow directions.** The six directions of the complex archimedean
flows: the three real directions `H`, `E`, `Fm` and their multiples `iH`, `iE`, `iFm` by `I`. -/
inductive ArchDirComplex where
  | H : ArchDirComplex
  | E : ArchDirComplex
  | Fm : ArchDirComplex
  | iH : ArchDirComplex
  | iE : ArchDirComplex
  | iFm : ArchDirComplex

/-- **Lower unipotent matrix.** The lower unipotent matrix `!![1, 0; x, 1]` in `GL (Fin 2) R`,
with inverse `!![1, 0; -x, 1]`. -/
def lowerUnipotentGL2 {R : Type*} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem lowerUnipotentGL2_zero {R : Type*} [CommRing R] :
    lowerUnipotentGL2 (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lowerUnipotentGL2]

theorem lowerUnipotentGL2_add {R : Type*} [CommRing R] (x y : R) :
    lowerUnipotentGL2 (x + y) = lowerUnipotentGL2 x * lowerUnipotentGL2 y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- **Real split torus element.** The split torus element `!![exp t, 0; 0, exp (-t)]` of
`GL (Fin 2) ℝ`. -/
def splitTorusGL2 (t : ℝ) : GL (Fin 2) ℝ where
  val := !![Real.exp t, 0; 0, Real.exp (-t)]
  inv := !![Real.exp (-t), 0; 0, Real.exp t]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

@[simp]
theorem splitTorusGL2_zero : splitTorusGL2 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitTorusGL2]

theorem splitTorusGL2_add (s t : ℝ) :
    splitTorusGL2 (s + t) = splitTorusGL2 s * splitTorusGL2 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add]
  ring

/-- **Complex split torus element.** The split torus element `!![exp z, 0; 0, exp (-z)]` of
`GL (Fin 2) ℂ`. -/
def splitTorusGL2Complex (z : ℂ) : GL (Fin 2) ℂ where
  val := !![Complex.exp z, 0; 0, Complex.exp (-z)]
  inv := !![Complex.exp (-z), 0; 0, Complex.exp z]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

@[simp]
theorem splitTorusGL2Complex_zero : splitTorusGL2Complex 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitTorusGL2Complex]

theorem splitTorusGL2Complex_add (z z' : ℂ) :
    splitTorusGL2Complex (z + z') = splitTorusGL2Complex z * splitTorusGL2Complex z' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2Complex, Matrix.mul_apply, Fin.sum_univ_two, Complex.exp_add]
  ring

/-- **Inclusion at a real place.** The inclusion of `GL (Fin 2) ℝ` into the adelic group at a
real infinite place `w`: the matrix sits at `w`, and every other component, at the other infinite
places and at the finite adeles, is the identity. -/
def archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) :
    GL (Fin 2) ℝ →* AdelicGL2 (𝓞 K) K :=
  (adelicArchGLInclAt K w).comp
    (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)

/-- **Inclusion at a complex place.** The inclusion of `GL (Fin 2) ℂ` into the adelic group at
a complex infinite place `w`: the matrix sits at `w`, and every other component, at the other
infinite places and at the finite adeles, is the identity. -/
def archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) :
    GL (Fin 2) ℂ →* AdelicGL2 (𝓞 K) K :=
  (adelicArchGLInclAt K w).comp
    (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom)

/-- **Real archimedean flow matrix.** The real flow in direction `d` at time `t`:
`splitTorusGL2 t` for `H`, `unipotentGL2 t` for `E` and `lowerUnipotentGL2 t` for `Fm`. -/
def archFlowMatrix : ArchDir → ℝ → GL (Fin 2) ℝ
  | .H, t => splitTorusGL2 t
  | .E, t => unipotentGL2 t
  | .Fm, t => lowerUnipotentGL2 t

/-- **Complex archimedean flow matrix.** The complex flow in direction `d` at time `t`:
`splitTorusGL2Complex t`, `unipotentGL2 t` and `lowerUnipotentGL2 t` for `H`, `E` and `Fm`, and
the same matrices at `t * I` for `iH`, `iE` and `iFm`. -/
def archFlowMatrixComplex : ArchDirComplex → ℝ → GL (Fin 2) ℂ
  | .H, t => splitTorusGL2Complex (t : ℂ)
  | .E, t => unipotentGL2 (t : ℂ)
  | .Fm, t => lowerUnipotentGL2 (t : ℂ)
  | .iH, t => splitTorusGL2Complex ((t : ℂ) * Complex.I)
  | .iE, t => unipotentGL2 ((t : ℂ) * Complex.I)
  | .iFm, t => lowerUnipotentGL2 ((t : ℂ) * Complex.I)

theorem archFlowMatrix_add (d : ArchDir) (s t : ℝ) :
    archFlowMatrix d (s + t) = archFlowMatrix d s * archFlowMatrix d t := by
  cases d
  · exact splitTorusGL2_add s t
  · exact unipotentGL2_add s t
  · exact lowerUnipotentGL2_add s t

theorem archFlowMatrixComplex_add (d : ArchDirComplex) (s t : ℝ) :
    archFlowMatrixComplex d (s + t)
      = archFlowMatrixComplex d s * archFlowMatrixComplex d t := by
  cases d
  · simpa [archFlowMatrixComplex] using splitTorusGL2Complex_add (s : ℂ) (t : ℂ)
  · simpa [archFlowMatrixComplex] using unipotentGL2_add (s : ℂ) (t : ℂ)
  · simpa [archFlowMatrixComplex] using lowerUnipotentGL2_add (s : ℂ) (t : ℂ)
  · have h : (((s + t : ℝ) : ℂ) * Complex.I)
        = (s : ℂ) * Complex.I + (t : ℂ) * Complex.I := by push_cast; ring
    simp only [archFlowMatrixComplex]
    rw [h]
    exact splitTorusGL2Complex_add _ _
  · have h : (((s + t : ℝ) : ℂ) * Complex.I)
        = (s : ℂ) * Complex.I + (t : ℂ) * Complex.I := by push_cast; ring
    simp only [archFlowMatrixComplex]
    rw [h]
    exact unipotentGL2_add _ _
  · have h : (((s + t : ℝ) : ℂ) * Complex.I)
        = (s : ℂ) * Complex.I + (t : ℂ) * Complex.I := by push_cast; ring
    simp only [archFlowMatrixComplex]
    rw [h]
    exact lowerUnipotentGL2_add _ _

/-- **Real archimedean flow at a real place.** The flow matrix `archFlowMatrix d t`, included
at the real place `w` by `archRealGLAt`. -/
def archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    AdelicGL2 (𝓞 K) K :=
  archRealGLAt K hw (archFlowMatrix d t)

/-- **Complex archimedean flow at a complex place.** The flow matrix
`archFlowMatrixComplex d t`, included at the complex place `w` by `archComplexGLAt`. -/
def archFlowAtComplex {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (t : ℝ) : AdelicGL2 (𝓞 K) K :=
  archComplexGLAt K hw (archFlowMatrixComplex d t)

theorem archFlowAt_add {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (s t : ℝ) :
    archFlowAt K hw d (s + t) = archFlowAt K hw d s * archFlowAt K hw d t := by
  rw [archFlowAt, archFlowAt, archFlowAt, archFlowMatrix_add, map_mul]

theorem archFlowAtComplex_add {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (s t : ℝ) :
    archFlowAtComplex K hw d (s + t)
      = archFlowAtComplex K hw d s * archFlowAtComplex K hw d t := by
  rw [archFlowAtComplex, archFlowAtComplex, archFlowAtComplex,
    archFlowMatrixComplex_add, map_mul]

section PlaceComponents

private theorem conjR {w : InfinitePlace K} (hw : w.IsReal) (f a : GL (Fin 2) ℝ) :
    (archRealGLAt K hw f)⁻¹ * archRealGLAt K hw a * archRealGLAt K hw f
      = archRealGLAt K hw (f⁻¹ * a * f) := by
  rw [map_mul, map_mul, map_inv]

private theorem conjC {w : InfinitePlace K} (hw : w.IsComplex) (f a : GL (Fin 2) ℂ) :
    (archComplexGLAt K hw f)⁻¹ * archComplexGLAt K hw a * archComplexGLAt K hw f
      = archComplexGLAt K hw (f⁻¹ * a * f) := by
  rw [map_mul, map_mul, map_inv]

end PlaceComponents

private theorem prod_ofFn_update {G : Type*} [Group G] :
    ∀ (n : ℕ) (f g : Fin n → G) (j : Fin n) (c : G),
      (∀ i, i ≠ j → g i = f i) → g j = f j * c →
        (List.ofFn g).prod = (List.ofFn f).prod *
          ((((List.ofFn f).drop (j.val + 1)).prod)⁻¹ * c *
            ((List.ofFn f).drop (j.val + 1)).prod)
  | 0, f, g, j, c, _, _ => j.elim0
  | n + 1, f, g, j, c, hne, hj => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    refine Fin.cases ?_ (fun j' => ?_) j hne hj
    · intro hne hj
      have htail : (List.ofFn fun i : Fin n => g i.succ)
          = List.ofFn fun i : Fin n => f i.succ := by
        congr 1; funext i; exact hne _ (Fin.succ_ne_zero i)
      rw [htail, hj]
      simp only [Fin.val_zero, zero_add, List.drop_succ_cons, List.drop_zero]
      group
    · intro hne hj
      have ih := prod_ofFn_update n (fun i => f i.succ) (fun i => g i.succ) j' c
        (fun i hi => hne _ fun h => hi (Fin.succ_injective _ h)) hj
      have h0 : g 0 = f 0 := hne 0 (Fin.succ_ne_zero j').symm
      rw [ih, h0]
      simp only [Fin.val_succ, List.drop_succ_cons, mul_assoc]

private theorem conj_list_prod {G M : Type*} [Group G] [Group M] (φ : M →* G) :
    ∀ (L : List (G × M)), (∀ p ∈ L, ∀ a : M, p.1⁻¹ * φ a * p.1 = φ (p.2⁻¹ * a * p.2)) →
      ∀ a : M, ((L.map Prod.fst).prod)⁻¹ * φ a * (L.map Prod.fst).prod =
        φ (((L.map Prod.snd).prod)⁻¹ * a * (L.map Prod.snd).prod)
  | [], _, a => by simp
  | p :: L, h, a => by
    have hp := h p List.mem_cons_self
    have ih := conj_list_prod φ L (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.prod_cons, mul_inv_rev]
    calc (L.map Prod.fst).prod⁻¹ * p.1⁻¹ * φ a * (p.1 * (L.map Prod.fst).prod)
        = (L.map Prod.fst).prod⁻¹ * (p.1⁻¹ * φ a * p.1) * (L.map Prod.fst).prod := by group
      _ = (L.map Prod.fst).prod⁻¹ * φ (p.2⁻¹ * a * p.2) * (L.map Prod.fst).prod := by rw [hp]
      _ = φ ((L.map Prod.snd).prod⁻¹ * (p.2⁻¹ * a * p.2) * (L.map Prod.snd).prod) := ih _
      _ = φ ((L.map Prod.snd).prod⁻¹ * p.2⁻¹ * a * (p.2 * (L.map Prod.snd).prod)) := by
          congr 1; group

open Classical in
/-- **Single-coordinate increment of an archimedean flow chart.** For a word `L₀` of real and
complex flow letters, the chart at times `t` is the product, in word order, of the flows of the
letters `L₀[i]` at the times `t i`. Adding `s` to the time of the letter `j` multiplies the chart
on the right by `T⁻¹ * flow(s) * T`, included at the place `w` of `L₀[j]`. Here `flow(s)` is the
flow matrix of `L₀[j]` at time `s`, and `T` is the product, in word order, of the flow matrices,
at their times `t i`, of the letters strictly after `j` that sit at the same place `w`; the letters
after `j` at other places do not enter `T`. -/
public theorem flowChart_add_single_eq_mul_conj
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (j : Fin L₀.length) (t : Fin L₀.length → ℝ) (s : ℝ) :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt K d.2.1 d.2.2 t)
        (fun d => archFlowAtComplex K d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun i => flow (L₀.get i) (t i)).prod
    let tailMatR : InfinitePlace K → GL (Fin 2) ℝ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inl d => if d.1 = w then archFlowMatrix d.2.2 (t i) else 1
        | Sum.inr _ => (1 : GL (Fin 2) ℝ)).drop (j.val + 1)).prod
    let tailMatC : InfinitePlace K → GL (Fin 2) ℂ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inr d => if d.1 = w then archFlowMatrixComplex d.2.2 (t i) else 1
        | Sum.inl _ => (1 : GL (Fin 2) ℂ)).drop (j.val + 1)).prod
    match L₀.get j with
    | Sum.inl d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archRealGLAt K d.2.1 ((tailMatR d.1)⁻¹ * archFlowMatrix d.2.2 s * tailMatR d.1)
    | Sum.inr d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archComplexGLAt K d.2.1
          ((tailMatC d.1)⁻¹ * archFlowMatrixComplex d.2.2 s * tailMatC d.1) := by
  intro flow chart tailMatR tailMatC
  have hfac : ∀ i : Fin L₀.length, i ≠ j →
      flow (L₀.get i) ((t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) i)
        = flow (L₀.get i) (t i) := by
    intro i hi
    simp [hi]
  have hj' : (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) j = t j + s := by simp
  have hprod : ∀ c : AdelicGL2 (𝓞 K) K, flow (L₀.get j) (t j + s) = flow (L₀.get j) (t j) * c →
      chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * ((((List.ofFn fun i => flow (L₀.get i) (t i)).drop (j.val + 1)).prod)⁻¹ * c *
          ((List.ofFn fun i => flow (L₀.get i) (t i)).drop (j.val + 1)).prod) := by
    intro c hc
    exact prod_ofFn_update L₀.length (fun i => flow (L₀.get i) (t i))
      (fun i => flow (L₀.get i) ((t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) i)) j c hfac
      (by change flow (L₀.get j) ((t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) j)
          = flow (L₀.get j) (t j) * c; rw [hj', hc])
  rcases hj : L₀.get j with ⟨w, hw, dj⟩ | ⟨w, hw, dj⟩
  · simp only
    have hsplit : flow (Sum.inl ⟨w, hw, dj⟩) (t j + s)
        = flow (Sum.inl ⟨w, hw, dj⟩) (t j) * archFlowAt K hw dj s := by
      change archFlowAt K hw dj (t j + s) = archFlowAt K hw dj (t j) * archFlowAt K hw dj s
      exact archFlowAt_add K hw dj (t j) s
    rw [hj] at hprod
    rw [hprod (archFlowAt K hw dj s) hsplit]
    congr 1
    let μ : Fin L₀.length → GL (Fin 2) ℝ := fun i => match L₀.get i with
      | Sum.inl d => if d.1 = w then archFlowMatrix d.2.2 (t i) else 1
      | Sum.inr _ => (1 : GL (Fin 2) ℝ)
    have key : ∀ (i : Fin L₀.length) (a : GL (Fin 2) ℝ),
        (flow (L₀.get i) (t i))⁻¹ * archRealGLAt K hw a * flow (L₀.get i) (t i)
          = archRealGLAt K hw ((μ i)⁻¹ * a * μ i) := by
      intro i a
      simp only [μ]
      rcases hi : L₀.get i with ⟨w', hw', di⟩ | ⟨w', hw', di⟩
      · simp only
        by_cases hww : w' = w
        · subst hww
          rw [ite_eq_left rfl]
          exact conjR K hw _ _
        · rw [ite_eq_right hww, inv_one, one_mul, mul_one]
          change (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ *
            adelicArchGLInclAt K w' _ = adelicArchGLInclAt K w _
          exact (adelicArchGLInclAt_commute K hww _ _).inv_mul_cancel
      · simp only [inv_one, one_mul, mul_one]
        have hww : w ≠ w' := fun h => by
          subst h; exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw') hw
        change (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _
          = adelicArchGLInclAt K w _
        exact (adelicArchGLInclAt_commute K (Ne.symm hww) _ _).inv_mul_cancel
    have hL := conj_list_prod (archRealGLAt K hw)
      (((List.ofFn fun i : Fin L₀.length => (flow (L₀.get i) (t i), μ i))).drop (j.val + 1))
      (fun p hp a => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hp)
        exact key i a)
      (archFlowMatrix dj s)
    rw [List.map_drop, List.map_drop, List.map_ofFn, List.map_ofFn] at hL
    exact hL
  · simp only
    have hsplit : flow (Sum.inr ⟨w, hw, dj⟩) (t j + s)
        = flow (Sum.inr ⟨w, hw, dj⟩) (t j) * archFlowAtComplex K hw dj s := by
      change archFlowAtComplex K hw dj (t j + s)
        = archFlowAtComplex K hw dj (t j) * archFlowAtComplex K hw dj s
      exact archFlowAtComplex_add K hw dj (t j) s
    rw [hj] at hprod
    rw [hprod (archFlowAtComplex K hw dj s) hsplit]
    congr 1
    let μ : Fin L₀.length → GL (Fin 2) ℂ := fun i => match L₀.get i with
      | Sum.inr d => if d.1 = w then archFlowMatrixComplex d.2.2 (t i) else 1
      | Sum.inl _ => (1 : GL (Fin 2) ℂ)
    have key : ∀ (i : Fin L₀.length) (a : GL (Fin 2) ℂ),
        (flow (L₀.get i) (t i))⁻¹ * archComplexGLAt K hw a * flow (L₀.get i) (t i)
          = archComplexGLAt K hw ((μ i)⁻¹ * a * μ i) := by
      intro i a
      simp only [μ]
      rcases hi : L₀.get i with ⟨w', hw', di⟩ | ⟨w', hw', di⟩
      · simp only [inv_one, one_mul, mul_one]
        have hww : w ≠ w' := fun h => by
          subst h; exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw) hw'
        change (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _
          = adelicArchGLInclAt K w _
        exact (adelicArchGLInclAt_commute K (Ne.symm hww) _ _).inv_mul_cancel
      · simp only
        by_cases hww : w' = w
        · subst hww
          rw [ite_eq_left rfl]
          exact conjC K hw _ _
        · rw [ite_eq_right hww, inv_one, one_mul, mul_one]
          change (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ *
            adelicArchGLInclAt K w' _ = adelicArchGLInclAt K w _
          exact (adelicArchGLInclAt_commute K hww _ _).inv_mul_cancel
    have hL := conj_list_prod (archComplexGLAt K hw)
      (((List.ofFn fun i : Fin L₀.length => (flow (L₀.get i) (t i), μ i))).drop (j.val + 1))
      (fun p hp a => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hp)
        exact key i a)
      (archFlowMatrixComplex dj s)
    rw [List.map_drop, List.map_drop, List.map_ofFn, List.map_ofFn] at hL
    exact hL

end AutomorphicForm

end
