/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean`,
`Definitions/Def_AutomorphicForm_ArchDerivCasimirComplex.lean`,
`Definitions/Def_AutomorphicForm_ArchType.lean`,
`Definitions/Def_AutomorphicForm_ConstantTerm.lean`,
`Theorems/Thm_AutomorphicForm_flowChart_add_single_eq_mul_conj.lean`
and
`P2M/Sol/S_AutomorphicForm_flowChart_add_single_eq_mul_conj.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import MathlibExt.NumberTheory.AutomorphicForm.FnTwist

import Mathlib.Tactic.Group

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K]

/-- The three real archimedean flow directions: split torus, upper
unipotent, and lower unipotent. -/
inductive ArchDir where
  | H : ArchDir
  | E : ArchDir
  | Fm : ArchDir

/-- The six complex archimedean flow directions: the three real directions
and their multiples by `I`. -/
inductive ArchDirComplex where
  | H : ArchDirComplex
  | E : ArchDirComplex
  | Fm : ArchDirComplex
  | iH : ArchDirComplex
  | iE : ArchDirComplex
  | iFm : ArchDirComplex

/-- The upper unipotent matrix `!![1, x; 0, 1]` in `GL (Fin 2) R`. -/
def unipotentGL2 {R : Type*} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower unipotent matrix `!![1, 0; x, 1]` in `GL (Fin 2) R`. -/
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
theorem unipotentGL2_zero {R : Type*} [CommRing R] :
    unipotentGL2 (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [unipotentGL2]

theorem unipotentGL2_add {R : Type*} [CommRing R] (x y : R) :
    unipotentGL2 (x + y) = unipotentGL2 x * unipotentGL2 y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[simp]
theorem lowerUnipotentGL2_zero {R : Type*} [CommRing R] :
    lowerUnipotentGL2 (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lowerUnipotentGL2]

theorem lowerUnipotentGL2_add {R : Type*} [CommRing R] (x y : R) :
    lowerUnipotentGL2 (x + y) = lowerUnipotentGL2 x * lowerUnipotentGL2 y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The real split torus element `!![exp t, 0; 0, exp (-t)]`. -/
def splitTorusGL2 (t : ℝ) : GL (Fin 2) ℝ where
  val := !![Real.exp t, 0; 0, Real.exp (-t)]
  inv := !![Real.exp (-t), 0; 0, Real.exp t]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

theorem splitTorusGL2_zero : splitTorusGL2 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitTorusGL2]

theorem splitTorusGL2_add (s t : ℝ) :
    splitTorusGL2 (s + t) = splitTorusGL2 s * splitTorusGL2 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add]
  ring

/-- The complex split torus element `!![exp z, 0; 0, exp (-z)]`. -/
def splitTorusGL2Complex (z : ℂ) : GL (Fin 2) ℂ where
  val := !![Complex.exp z, 0; 0, Complex.exp (-z)]
  inv := !![Complex.exp (-z), 0; 0, Complex.exp z]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

theorem splitTorusGL2Complex_zero : splitTorusGL2Complex 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitTorusGL2Complex]

theorem splitTorusGL2Complex_add (z z' : ℂ) :
    splitTorusGL2Complex (z + z') = splitTorusGL2Complex z * splitTorusGL2Complex z' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2Complex, Matrix.mul_apply, Fin.sum_univ_two, Complex.exp_add]
  ring

/-- Inclusion of a real `2 × 2` matrix at a real infinite place into the
adelic group. -/
def archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) :
    GL (Fin 2) ℝ →* AdelicGL2 (𝓞 K) K :=
  (adelicArchGLInclAt K w).comp
    (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)

/-- Inclusion of a complex `2 × 2` matrix at a complex infinite place into
the adelic group. -/
def archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) :
    GL (Fin 2) ℂ →* AdelicGL2 (𝓞 K) K :=
  (adelicArchGLInclAt K w).comp
    (Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom)

/-- The real archimedean flow matrix in direction `d` at time `t`. -/
def archFlowMatrix : ArchDir → ℝ → GL (Fin 2) ℝ
  | .H, t => splitTorusGL2 t
  | .E, t => unipotentGL2 t
  | .Fm, t => lowerUnipotentGL2 t

/-- The complex archimedean flow matrix in direction `d` at time `t`. -/
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

/-- The real archimedean flow at a real place, as an adelic element. -/
def archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    AdelicGL2 (𝓞 K) K :=
  archRealGLAt K hw (archFlowMatrix d t)

/-- The complex archimedean flow at a complex place, as an adelic element. -/
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

private def archEvalOf (w : InfinitePlace K) : InfiniteAdeleRing K →+* w.Completion where
  toFun a := a w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem archEvalOf_apply (w : InfinitePlace K) (a : InfiniteAdeleRing K) :
    archEvalOf K w a = a w :=
  rfl

private def archComp (w : InfinitePlace K) :
    GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (archEvalOf K w)

private theorem archMatrixUpdate_apply {w v : InfinitePlace K}
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2) :
    archMatrixUpdate K w m i j v
      = Function.update
          (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w m v i j := by
  have h := (archMatrixPiEquiv K).apply_symm_apply
    (Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w m)
  have hv := congrFun h v
  exact congrFun (congrFun hv i) j

private theorem archComp_archGLIncl_self (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    archComp K w (archGLIncl K w k) = k := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show (archEvalOf K w) (((archGLIncl K w k : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j)
      = (k : Matrix (Fin 2) (Fin 2) w.Completion) i j
  rw [archEvalOf_apply, show ((archGLIncl K w k : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
      = archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j from rfl,
    archMatrixUpdate_apply]
  simp

private theorem archComp_archGLIncl_of_ne {v w : InfinitePlace K} (hvw : v ≠ w)
    (k : GL (Fin 2) w.Completion) :
    archComp K v (archGLIncl K w k) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show (archEvalOf K v) (((archGLIncl K w k : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j)
      = (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j
  rw [archEvalOf_apply, show ((archGLIncl K w k : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
      = archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j from rfl,
    archMatrixUpdate_apply]
  simp [Function.update_of_ne hvw]

private def glArchOf :
    GL (Fin 2) (AdeleRing (𝓞 K) K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map
    { toFun := fun a : AdeleRing (𝓞 K) K => a.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

private def glFinOf :
    GL (Fin 2) (AdeleRing (𝓞 K) K) →* GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map
    { toFun := fun a : AdeleRing (𝓞 K) K => a.2
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

private theorem glArchOf_adelicArchGLIncl (k : GL (Fin 2) (InfiniteAdeleRing K)) :
    glArchOf K (adelicArchGLIncl K k) = k := by
  ext i j; rfl

private theorem glFinOf_adelicArchGLIncl (k : GL (Fin 2) (InfiniteAdeleRing K)) :
    glFinOf K (adelicArchGLIncl K k) = 1 := by
  ext i j; rfl

private theorem eq_of_glArchOf_eq_of_glFinOf_eq {x y : AdelicGL2 (𝓞 K) K}
    (h₁ : glArchOf K x = glArchOf K y) (h₂ : glFinOf K x = glFinOf K y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing K) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₂
  exact Prod.ext h₁' h₂'

private theorem eq_of_forall_archComp_eq {g h : GL (Fin 2) (InfiniteAdeleRing K)}
    (hc : ∀ w : InfinitePlace K, archComp K w g = archComp K w h) : g = h := by
  apply Units.ext
  ext i j
  funext w
  have := congrArg
    (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (hc w)
  exact this

private theorem placed_comm_of_ne {w w' : InfinitePlace K} (hww : w ≠ w')
    (a : GL (Fin 2) w.Completion) (b : GL (Fin 2) w'.Completion) :
    adelicArchGLInclAt K w a * adelicArchGLInclAt K w' b
      = adelicArchGLInclAt K w' b * adelicArchGLInclAt K w a := by
  refine eq_of_glArchOf_eq_of_glFinOf_eq K ?_ ?_
  · rw [map_mul, map_mul]
    refine eq_of_forall_archComp_eq K fun v => ?_
    rw [map_mul, map_mul]
    show archComp K v (glArchOf K (adelicArchGLIncl K (archGLIncl K w a))) *
        archComp K v (glArchOf K (adelicArchGLIncl K (archGLIncl K w' b))) =
      archComp K v (glArchOf K (adelicArchGLIncl K (archGLIncl K w' b))) *
        archComp K v (glArchOf K (adelicArchGLIncl K (archGLIncl K w a)))
    rw [glArchOf_adelicArchGLIncl K (archGLIncl K w a),
      glArchOf_adelicArchGLIncl K (archGLIncl K w' b)]
    by_cases hv : v = w
    · subst hv
      rw [archComp_archGLIncl_of_ne K hww, mul_one, one_mul]
    · rw [archComp_archGLIncl_of_ne K hv, one_mul, mul_one]
  · rw [map_mul, map_mul,
      show glFinOf K (adelicArchGLInclAt K w a) = 1 from
        glFinOf_adelicArchGLIncl K (archGLIncl K w a),
      show glFinOf K (adelicArchGLInclAt K w' b) = 1 from
        glFinOf_adelicArchGLIncl K (archGLIncl K w' b)]

private theorem conj_eq_self_of_ne {w w' : InfinitePlace K} (hww : w ≠ w')
    (f : GL (Fin 2) w'.Completion) (a : GL (Fin 2) w.Completion) :
    (adelicArchGLInclAt K w' f)⁻¹ * adelicArchGLInclAt K w a * adelicArchGLInclAt K w' f
      = adelicArchGLInclAt K w a := by
  rw [mul_assoc, placed_comm_of_ne K hww a f, ← mul_assoc, inv_mul_cancel, one_mul]

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

/-- A single-coordinate increment of an archimedean flow chart is the chart
times the incremented flow conjugated by the tail product. -/
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
      (by show flow (L₀.get j) ((t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) j)
          = flow (L₀.get j) (t j) * c; rw [hj', hc])
  rcases hj : L₀.get j with ⟨w, hw, dj⟩ | ⟨w, hw, dj⟩
  · simp only
    have hsplit : flow (Sum.inl ⟨w, hw, dj⟩) (t j + s)
        = flow (Sum.inl ⟨w, hw, dj⟩) (t j) * archFlowAt K hw dj s := by
      show archFlowAt K hw dj (t j + s) = archFlowAt K hw dj (t j) * archFlowAt K hw dj s
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
          rw [if_pos rfl]
          exact conjR K hw _ _
        · rw [if_neg hww, inv_one, one_mul, mul_one]
          show (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _
            = adelicArchGLInclAt K w _
          exact conj_eq_self_of_ne K (Ne.symm hww) _ _
      · simp only [inv_one, one_mul, mul_one]
        have hww : w ≠ w' := fun h => by
          subst h; exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw') hw
        show (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _
          = adelicArchGLInclAt K w _
        exact conj_eq_self_of_ne K hww _ _
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
      show archFlowAtComplex K hw dj (t j + s)
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
        show (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _
          = adelicArchGLInclAt K w _
        exact conj_eq_self_of_ne K hww _ _
      · simp only
        by_cases hww : w' = w
        · subst hww
          rw [if_pos rfl]
          exact conjC K hw _ _
        · rw [if_neg hww, inv_one, one_mul, mul_one]
          show (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _
            = adelicArchGLInclAt K w _
          exact conj_eq_self_of_ne K (Ne.symm hww) _ _
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
