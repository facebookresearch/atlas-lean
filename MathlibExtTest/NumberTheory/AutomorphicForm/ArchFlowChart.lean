/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.ArchFlowChart

@[expose] public section

open NumberField AutomorphicForm
open scoped Classical

namespace AutomorphicForm

set_option maxHeartbeats 1600000 in
/-- Consumer with the original `Type` binders. -/
theorem exactSource (K : Type) [Field K] [NumberField K]
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
          ((tailMatC d.1)⁻¹ * archFlowMatrixComplex d.2.2 s * tailMatC d.1) :=
  flowChart_add_single_eq_mul_conj K L₀ j t s

set_option maxHeartbeats 1600000 in
/-- Higher-universe consumer. -/
theorem exactSource_univ (K : Type 1) [Field K] [NumberField K]
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
          ((tailMatC d.1)⁻¹ * archFlowMatrixComplex d.2.2 s * tailMatC d.1) :=
  flowChart_add_single_eq_mul_conj K L₀ j t s

/-- Boundary example: with a single real letter, the tail is empty, so the
increment is unconjugated. -/
example (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (d : ArchDir) (t s : ℝ) :
    archFlowAt K hw d (t + s) = archFlowAt K hw d t * archFlowAt K hw d s :=
  archFlowAt_add K hw d t s

end AutomorphicForm
