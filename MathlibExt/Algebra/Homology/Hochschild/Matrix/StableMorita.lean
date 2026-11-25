/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Morita
public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension.Trace
public import MathlibExt.Algebra.Homology.ExactColimits
public import MathlibExt.Algebra.Homology.NatIsoOfQuasiIsoAt
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Colimits of finite matrix Hochschild complexes

Top-left zero extensions give a diagram of positive-size matrix Hochschild
complexes. Its finite traces and corners assemble into maps on reindexings
of this diagram. For a connected shape with exact colimits, the homology of
this colimit model is the original coefficient homology, through the actual
trace and corner maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MulOpposite
open scoped BigOperators TensorProduct

universe t u v w j j'

namespace ModuleCat.Algebra.Hochschild.Matrix.StableMorita

variable (k : Type u) [CommRing k]
  (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]

private theorem zeroExtend_nonempty_word {r s : ℕ} (h : r ≤ s) :
    ∀ (n : ℕ) (U₀ : Matrix (Fin r) (Fin r) k) (U : Fin n → Matrix (Fin r) (Fin r) k),
      Matrix.zeroExtend h (U₀ * (List.ofFn U).prod) =
        Matrix.zeroExtend h U₀ * (List.ofFn (fun i => Matrix.zeroExtend h (U i))).prod := by
  intro n
  induction n with
  | zero =>
    intro U₀ U
    simp
  | succ n ih =>
    intro U₀ U
    obtain ⟨V₀, V, rfl⟩ := Fin.exists_cons U
    have hc : (fun i : Fin (n + 1) => Matrix.zeroExtend h
        ((Fin.cons (α := fun _ => Matrix (Fin r) (Fin r) k) V₀ V) i)) =
        Fin.cons (α := fun _ => Matrix (Fin s) (Fin s) k)
          (Matrix.zeroExtend h V₀) (fun i => Matrix.zeroExtend h (V i)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hc, List.ofFn_cons, List.ofFn_cons, List.prod_cons, List.prod_cons,
      Matrix.zeroExtend_mul, ih]

private theorem zeroExtend_scaled {N : Type*} [AddCommGroup N] [Module k N]
    {r s : ℕ} (h : r ≤ s) (U : Matrix (Fin r) (Fin r) k) (x : N) :
    Matrix.zeroExtend h (U.map (fun c => c • x)) =
      (Matrix.zeroExtend h U).map (fun c => c • x) := by
  ext i l
  by_cases hi : i.val < r <;> by_cases hl : l.val < r <;>
    simp only [Matrix.zeroExtend_apply, Matrix.map_apply, hi, hl, ↓reduceDIte, zero_smul]

/-- Finite generalized trace commutes with the actual tensor zero-extension map. -/
theorem generalizedTrace_zeroExtend {r s : ℕ} (h : r ≤ s) (n : ℕ) :
    (generalizedTrace k (Fin s) n).comp
      (TensorProduct.map (Matrix.zeroExtendLinear (k := k) (A := M) h)
        (PiTensorProduct.map fun _ : Fin n => Matrix.zeroExtendLinear (k := k) (A := A) h)) =
      generalizedTrace k (Fin r) n := by
  apply matrix_tensor_ext k A M (Fin r)
  intro U₀ m U a
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
    Matrix.zeroExtendLinear_apply]
  rw [zeroExtend_scaled k h U₀ m]
  have hU : (fun l : Fin n => Matrix.zeroExtend h ((U l).map (fun c => c • a l))) =
      (fun l => (Matrix.zeroExtend h (U l)).map (fun c => c • a l)) := by
    funext l
    exact zeroExtend_scaled k h (U l) (a l)
  rw [hU,
    generalizedTrace_scaled k (Fin s) n (Matrix.zeroExtend h U₀)
      (fun i => Matrix.zeroExtend h (U i)) m a,
    generalizedTrace_scaled k (Fin r) n U₀ U m a,
    ← zeroExtend_nonempty_word k h n U₀ U, Matrix.zeroExtend_trace]

variable [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

attribute [local instance] Coefficients.leftModule Coefficients.rightModule
  Coefficients.commute Coefficients.leftTower Coefficients.rightTower
  ModuleCat.Algebra.Hochschild.uliftSMulCommClass

private theorem sum_truncate {N : Type*} [AddCommGroup N]
    {r s : ℕ} (h : r ≤ s) (f : Fin r → N) :
    (∑ i : Fin s, if hi : i.val < r then f ⟨i.val, hi⟩ else 0) = ∑ i : Fin r, f i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.sum_trunc _ (by
    intro i
    simp only [Fin.val_natAdd,
      dite_eq_right (Nat.not_lt.mpr (Nat.le_add_right r i.val))])]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_castAdd, dite_eq_left i.is_lt]

private theorem zeroExtend_left {r s : ℕ} (h : r ≤ s)
    (B : Matrix (Fin r) (Fin r) A) (X : Matrix (Fin r) (Fin r) M) :
    Matrix.zeroExtend h B • Matrix.zeroExtend h X = Matrix.zeroExtend h (B • X) := by
  ext i l
  rw [Coefficients.left_smul_apply]
  by_cases hi : i.val < r
  · by_cases hl : l.val < r
    · rw [Matrix.zeroExtend_apply, dite_eq_left hi, dite_eq_left hl,
        Coefficients.left_smul_apply]
      calc
        _ = ∑ p : Fin s, if hp : p.val < r then
            B ⟨i.val, hi⟩ ⟨p.val, hp⟩ • X ⟨p.val, hp⟩ ⟨l.val, hl⟩ else 0 := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hp : p.val < r <;>
            simp only [Matrix.zeroExtend_apply, hi, hl, hp, ↓reduceDIte, smul_zero]
        _ = _ := sum_truncate h (fun p : Fin r => B ⟨i.val, hi⟩ p • X p ⟨l.val, hl⟩)
    · rw [Matrix.zeroExtend_of_col h _ i l (Nat.le_of_not_gt hl)]
      apply Finset.sum_eq_zero
      intro p _
      rw [Matrix.zeroExtend_of_col h X p l (Nat.le_of_not_gt hl), smul_zero]
  · rw [Matrix.zeroExtend_of_row h _ i l (Nat.le_of_not_gt hi)]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.zeroExtend_of_row h B i p (Nat.le_of_not_gt hi), zero_smul]

private theorem zeroExtend_right {r s : ℕ} (h : r ≤ s)
    (B : Matrix (Fin r) (Fin r) A) (X : Matrix (Fin r) (Fin r) M) :
    op (Matrix.zeroExtend h B) • Matrix.zeroExtend h X = Matrix.zeroExtend h (op B • X) := by
  ext i l
  rw [Coefficients.right_smul_apply]
  by_cases hi : i.val < r
  · by_cases hl : l.val < r
    · rw [Matrix.zeroExtend_apply, dite_eq_left hi, dite_eq_left hl,
        Coefficients.right_smul_apply]
      calc
        _ = ∑ p : Fin s, if hp : p.val < r then
            op (B ⟨p.val, hp⟩ ⟨l.val, hl⟩) • X ⟨i.val, hi⟩ ⟨p.val, hp⟩ else 0 := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hp : p.val < r <;>
            simp only [Matrix.zeroExtend_apply, hi, hl, hp, ↓reduceDIte, op_zero, smul_zero]
        _ = _ := sum_truncate h (fun p : Fin r => op (B p ⟨l.val, hl⟩) • X ⟨i.val, hi⟩ p)
    · rw [Matrix.zeroExtend_of_col h _ i l (Nat.le_of_not_gt hl)]
      apply Finset.sum_eq_zero
      intro p _
      rw [Matrix.zeroExtend_of_col h B p l (Nat.le_of_not_gt hl), op_zero, zero_smul]
  · rw [Matrix.zeroExtend_of_row h _ i l (Nat.le_of_not_gt hi)]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.zeroExtend_of_row h X i p (Nat.le_of_not_gt hi), smul_zero]

/-- The finite transition uses the nonunital algebra map given by top-left zero extension. -/
def finiteTransitionAt {r s : ℕ} (h : r ≤ s) :
    chainComplex k (Matrix (Fin (r + 1)) (Fin (r + 1)) A)
        (ULift.{max u v w t} (Matrix (Fin (r + 1)) (Fin (r + 1)) M)) ⟶
      chainComplex k (Matrix (Fin (s + 1)) (Fin (s + 1)) A)
        (ULift.{max u v w t} (Matrix (Fin (s + 1)) (Fin (s + 1)) M)) :=
  liftedMapAt.{t} (Matrix.zeroExtendAlgHom (k := k) (A := A) (Nat.succ_le_succ h))
    (Matrix.zeroExtendLinear (k := k) (A := M) (Nat.succ_le_succ h))
    (fun B X => (zeroExtend_left (A := A) (M := M) (Nat.succ_le_succ h) B X).symm)
    (fun B X => (zeroExtend_right (A := A) (M := M) (Nat.succ_le_succ h) B X).symm)

/-- Each finite transition retains its literal matrix entries in tensor coordinates. -/
theorem finiteTransitionAt_f_tprod {r s : ℕ} (h : r ≤ s) (n : ℕ)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) M)
    (a : Fin n → Matrix (Fin (r + 1)) (Fin (r + 1)) A) :
    ((finiteTransitionAt.{t} k A M h).f n).hom
      (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up (Matrix.zeroExtend (Nat.succ_le_succ h) X) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i => Matrix.zeroExtend (Nat.succ_le_succ h) (a i)) := by
  simpa only [finiteTransitionAt, Matrix.zeroExtendAlgHom_apply,
    Matrix.zeroExtendLinear_apply] using
    (liftedMapAt_f_tprod.{_, _, _, _, _, t}
      (Matrix.zeroExtendAlgHom (k := k) (A := A) (Nat.succ_le_succ h))
      (Matrix.zeroExtendLinear (k := k) (A := M) (Nat.succ_le_succ h))
      (fun B X => (zeroExtend_left (A := A) (M := M) (Nat.succ_le_succ h) B X).symm)
      (fun B X => (zeroExtend_right (A := A) (M := M) (Nat.succ_le_succ h) B X).symm)
      n (ULift.up X) a)

private theorem finiteTransitionAt_self (r : ℕ) :
    finiteTransitionAt.{t} k A M (le_rfl : r ≤ r) =
      𝟙 (chainComplex k (Matrix (Fin (r + 1)) (Fin (r + 1)) A)
        (ULift.{max u v w t} (Matrix (Fin (r + 1)) (Fin (r + 1)) M))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro X a
  rcases X with ⟨X⟩
  simp only [finiteTransitionAt_f_tprod, Matrix.zeroExtend_self,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]

private theorem finiteTransitionAt_comp {r s q : ℕ} (h : r ≤ s) (h' : s ≤ q) :
    finiteTransitionAt.{t} k A M h ≫ finiteTransitionAt.{t} k A M h' =
      finiteTransitionAt.{t} k A M (h.trans h') := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro X a
  rcases X with ⟨X⟩
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [finiteTransitionAt_f_tprod, finiteTransitionAt_f_tprod, finiteTransitionAt_f_tprod]
  simp only [Matrix.zeroExtend_comp]

/-- Positive-size finite matrix Hochschild complexes with their actual zero extensions. -/
def finiteDiagramAt : ℕ ⥤ ChainComplex (ModuleCat.{max u v w t} k) ℕ where
  obj r := chainComplex k (Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (ULift.{max u v w t} (Matrix (Fin (r + 1)) (Fin (r + 1)) M))
  map h := finiteTransitionAt.{t} k A M (leOfHom h)
  map_id r := finiteTransitionAt_self.{t} k A M r
  map_comp f g := (finiteTransitionAt_comp.{t} k A M (leOfHom f) (leOfHom g)).symm

/-- The actual finite trace commutes with every positive-size matrix transition. -/
theorem finiteTransitionAt_comp_trace {r s : ℕ} (h : r ≤ s) :
    finiteTransitionAt.{t} k A M h ≫ traceChainMapAt.{t} k A M (Fin (s + 1)) =
      traceChainMapAt.{t} k A M (Fin (r + 1)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro X a
  rcases X with ⟨X⟩
  let e : ULift.{max u v w t} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A := coefficientUnliftEquiv k A M n
  apply e.injective
  change e (traceLinearLiftAt.{t} k A M (Fin (s + 1)) n
      (((finiteTransitionAt.{t} k A M h).f n).hom
        (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a))) =
    e (traceLinearLiftAt.{t} k A M (Fin (r + 1)) n
      (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a))
  rw [finiteTransitionAt_f_tprod, traceLinearLiftAt_down, traceLinearLiftAt_down,
    coefficientUnliftEquiv_tprod, coefficientUnliftEquiv_tprod]
  simpa only [LinearMap.comp_apply, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
    Matrix.zeroExtendLinear_apply] using
    LinearMap.congr_fun (generalizedTrace_zeroExtend k A M (Nat.succ_le_succ h) n)
      (X ⊗ₜ[k] PiTensorProduct.tprod k a)

private theorem zeroExtend_corner {r s : ℕ} (h : r ≤ s) {N : Type*}
    [AddCommGroup N] [Module k N] (x : N) :
    Matrix.zeroExtend (Nat.succ_le_succ h) (cornerLinear k (Fin (r + 1)) 0 x) =
      cornerLinear k (Fin (s + 1)) 0 x := by
  ext i l
  by_cases hi : i.val < r + 1
  · by_cases hl : l.val < r + 1
    · simp only [Matrix.zeroExtend_apply, hi, hl, ↓reduceDIte, cornerLinear_apply,
        Fin.ext_iff, Fin.val_mk, Fin.val_zero]
    · have hl0 : l ≠ 0 := by
        intro he
        subst l
        exact hl (Nat.succ_pos r)
      simp only [Matrix.zeroExtend_apply, hi, hl, ↓reduceDIte, cornerLinear_apply,
        hl0, ite_false, ite_self]
  · have hi0 : i ≠ 0 := by
      intro he
      subst i
      exact hi (Nat.succ_pos r)
    simp only [Matrix.zeroExtend_apply, hi, ↓reduceDIte, cornerLinear_apply, hi0, ite_false]

/-- The zeroth corner is preserved by the finite zero-extension transitions. -/
theorem corner_comp_finiteTransitionAt {r s : ℕ} (h : r ≤ s) :
    Morita.cornerChainMapAt.{t} k A M (Fin (r + 1)) 0 ≫ finiteTransitionAt.{t} k A M h =
      Morita.cornerChainMapAt.{t} k A M (Fin (s + 1)) 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro m a
  rcases m with ⟨m⟩
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [Morita.cornerChainMapAt_f_tprod, finiteTransitionAt_f_tprod,
    Morita.cornerChainMapAt_f_tprod]
  simp only [zeroExtend_corner]

/-- Finite trace is a natural transformation to the original coefficient complex. -/
def traceNatAt : finiteDiagramAt.{t} k A M ⟶
    (Functor.const ℕ).obj (chainComplex k A (ULift.{max u v w t} M)) where
  app r := traceChainMapAt.{t} k A M (Fin (r + 1))
  naturality := by
    intro r s h
    change finiteTransitionAt.{t} k A M (leOfHom h) ≫
        traceChainMapAt.{t} k A M (Fin (s + 1)) =
      traceChainMapAt.{t} k A M (Fin (r + 1)) ≫ 𝟙 _
    rw [Category.comp_id]
    exact finiteTransitionAt_comp_trace.{t} k A M (leOfHom h)

/-- The zeroth corner is a natural transformation into the positive-size matrix diagram. -/
def cornerNatAt :
    (Functor.const ℕ).obj (chainComplex k A (ULift.{max u v w t} M)) ⟶
      finiteDiagramAt.{t} k A M where
  app r := Morita.cornerChainMapAt.{t} k A M (Fin (r + 1)) 0
  naturality := by
    intro r s h
    change 𝟙 _ ≫ Morita.cornerChainMapAt.{t} k A M (Fin (s + 1)) 0 =
      Morita.cornerChainMapAt.{t} k A M (Fin (r + 1)) 0 ≫
        finiteTransitionAt.{t} k A M (leOfHom h)
    rw [Category.id_comp]
    exact (corner_comp_finiteTransitionAt.{t} k A M (leOfHom h)).symm

variable {J : Type j} [Category.{j'} J]

/-- The earned finite trace isomorphisms form a natural homology isomorphism. -/
def traceHomologyNatIsoAt (G : J ⥤ ℕ) (n : ℕ) :
    (G ⋙ finiteDiagramAt.{t} k A M) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
          (ComplexShape.down ℕ) n ≅
      (Functor.const J).obj ((chainComplex k A (ULift.{max u v w t} M)).homology n) :=
  HomologicalComplex.homologyNatIsoOfQuasiIsoAt
    (Functor.whiskerLeft G (traceNatAt.{t} k A M)) n (fun r => by
      apply (quasiIsoAt_iff_isIso_homologyMap _ n).2
      exact (Morita.finiteHomologyIsoAt.{t} k A M (Fin (G.obj r + 1)) 0 n).isIso_hom)

@[simp]
theorem traceHomologyNatIsoAt_hom_app (G : J ⥤ ℕ) (n : ℕ) (r : J) :
    (traceHomologyNatIsoAt.{t} k A M G n).hom.app r =
      HomologicalComplex.homologyMap (traceChainMapAt.{t} k A M (Fin (G.obj r + 1))) n := rfl

variable [HasColimitsOfShape J (ModuleCat.{max u v w t} k)]

/-- The stable colimit model of a reindexed positive-size finite matrix diagram. -/
def stableComplexAt (G : J ⥤ ℕ) : ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
  colimit (G ⋙ finiteDiagramAt.{t} k A M)

private def traceCoconeAt (G : J ⥤ ℕ) : Cocone (G ⋙ finiteDiagramAt.{t} k A M) where
  pt := chainComplex k A (ULift.{max u v w t} M)
  ι := Functor.whiskerLeft G (traceNatAt.{t} k A M)

/-- The colimit trace is induced by the actual finite trace maps. -/
def stableTraceAt (G : J ⥤ ℕ) :
    stableComplexAt.{t} k A M G ⟶ chainComplex k A (ULift.{max u v w t} M) :=
  colimit.desc _ (traceCoconeAt.{t} k A M G)

@[reassoc]
theorem ι_stableTraceAt (G : J ⥤ ℕ) (r : J) :
    colimit.ι (G ⋙ finiteDiagramAt.{t} k A M) r ≫ stableTraceAt.{t} k A M G =
      traceChainMapAt.{t} k A M (Fin (G.obj r + 1)) :=
  colimit.ι_desc _ _ r

/-- A transformation of indexing functors induces the actual colimit transition map. -/
def stableMapAt {G G' : J ⥤ ℕ} (τ : G ⟶ G') :
    stableComplexAt.{t} k A M G ⟶ stableComplexAt.{t} k A M G' :=
  colimMap (Functor.whiskerRight τ (finiteDiagramAt.{t} k A M))

@[reassoc]
theorem stableMapAt_comp_trace {G G' : J ⥤ ℕ} (τ : G ⟶ G') :
    stableMapAt.{t} k A M τ ≫ stableTraceAt.{t} k A M G' = stableTraceAt.{t} k A M G := by
  apply colimit.hom_ext
  intro r
  change colimit.ι (G ⋙ finiteDiagramAt.{t} k A M) r ≫
      colimMap (Functor.whiskerRight τ (finiteDiagramAt.{t} k A M)) ≫
        stableTraceAt.{t} k A M G' =
    colimit.ι (G ⋙ finiteDiagramAt.{t} k A M) r ≫ stableTraceAt.{t} k A M G
  rw [ι_colimMap_assoc, ι_stableTraceAt, ι_stableTraceAt]
  exact finiteTransitionAt_comp_trace.{t} k A M (leOfHom (τ.app r))

variable [IsConnected J]

private def constantColimitIsoAt :
    colimit ((Functor.const J).obj (chainComplex k A (ULift.{max u v w t} M))) ≅
      chainComplex k A (ULift.{max u v w t} M) :=
  colimit.isoColimitCocone ⟨constCocone J _, isColimitConstCocone J _⟩

private theorem constantColimitIsoAt_leg (r : J) :
    colimit.ι ((Functor.const J).obj (chainComplex k A (ULift.{max u v w t} M))) r ≫
        (constantColimitIsoAt.{t} (J := J) k A M).hom =
      𝟙 (chainComplex k A (ULift.{max u v w t} M)) :=
  colimit.isoColimitCocone_ι_hom _ r

private theorem constantColimitIsoAt_inv_eq_ι (r : J) :
    (constantColimitIsoAt.{t} (J := J) k A M).inv =
      colimit.ι ((Functor.const J).obj (chainComplex k A (ULift.{max u v w t} M))) r := by
  apply (cancel_mono (constantColimitIsoAt.{t} (J := J) k A M).hom).mp
  rw [Iso.inv_hom_id, constantColimitIsoAt_leg]

/-- The stable corner is induced by the coherent zeroth finite corners. -/
def stableCornerAt (G : J ⥤ ℕ) :
    chainComplex k A (ULift.{max u v w t} M) ⟶ stableComplexAt.{t} k A M G :=
  (constantColimitIsoAt.{t} (J := J) k A M).inv ≫
    colimMap (Functor.whiskerLeft G (cornerNatAt.{t} k A M))

/-- The stable corner is the same actual corner through every finite stage. -/
theorem stableCornerAt_eq_stage (G : J ⥤ ℕ) (r : J) :
    stableCornerAt.{t} k A M G =
      Morita.cornerChainMapAt.{t} k A M (Fin (G.obj r + 1)) 0 ≫
        colimit.ι (G ⋙ finiteDiagramAt.{t} k A M) r := by
  change (constantColimitIsoAt.{t} (J := J) k A M).inv ≫
      colimMap (Functor.whiskerLeft G (cornerNatAt.{t} k A M)) = _
  rw [constantColimitIsoAt_inv_eq_ι k A M r]
  simpa only [colimMap_eq] using
    ι_colimMap (Functor.whiskerLeft G (cornerNatAt.{t} k A M)) r

/-- The stable corner followed by trace is the identity chain map. -/
theorem stableCornerAt_comp_trace (G : J ⥤ ℕ) :
    stableCornerAt.{t} k A M G ≫ stableTraceAt.{t} k A M G =
      𝟙 (chainComplex k A (ULift.{max u v w t} M)) := by
  let r : J := Classical.arbitrary J
  rw [stableCornerAt_eq_stage k A M G r, Category.assoc, ι_stableTraceAt,
    Morita.cornerChainMapAt_comp_trace]

variable [HasExactColimitsOfShape J (ModuleCat.{max u v w t} k)]

/-- Exact connected colimits of finite matrix chains have the original coefficient homology. -/
def stableHomologyIsoAt (G : J ⥤ ℕ) (n : ℕ) :
    (stableComplexAt.{t} k A M G).homology n ≅
      (chainComplex k A (ULift.{max u v w t} M)).homology n :=
  HomologicalComplex.homologyColimitIso (G ⋙ finiteDiagramAt.{t} k A M) n ≪≫
    (colim (J := J) (C := ModuleCat.{max u v w t} k)).mapIso
      (traceHomologyNatIsoAt.{t} k A M G n) ≪≫
    colimit.isoColimitCocone ⟨constCocone J _, isColimitConstCocone J _⟩

/-- The chosen homology comparison is the homology map of the actual colimit trace. -/
theorem stableHomologyIsoAt_hom (G : J ⥤ ℕ) (n : ℕ) :
    (stableHomologyIsoAt.{t} k A M G n).hom =
      HomologicalComplex.homologyMap (stableTraceAt.{t} k A M G) n := by
  rw [← cancel_epi (HomologicalComplex.homologyColimitIso
    (G ⋙ finiteDiagramAt.{t} k A M) n).inv]
  simp only [stableHomologyIsoAt, Iso.trans_hom, Iso.inv_hom_id_assoc]
  apply colimit.hom_ext
  intro r
  have hl : colimit.ι ((G ⋙ finiteDiagramAt.{t} k A M) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
          (ComplexShape.down ℕ) n) r ≫
      ((colim (J := J) (C := ModuleCat.{max u v w t} k)).mapIso
        (traceHomologyNatIsoAt.{t} k A M G n)).hom ≫
      (colimit.isoColimitCocone
        ⟨constCocone J _, isColimitConstCocone J _⟩).hom =
      HomologicalComplex.homologyMap (traceChainMapAt.{t} k A M (Fin (G.obj r + 1))) n := by
    rw [Functor.mapIso_hom, ← colimMap_eq, ι_colimMap_assoc,
      colimit.isoColimitCocone_ι_hom, constCocone_ι, NatTrans.id_app, Category.comp_id,
      traceHomologyNatIsoAt_hom_app]
  have hr : colimit.ι ((G ⋙ finiteDiagramAt.{t} k A M) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
          (ComplexShape.down ℕ) n) r ≫
      (HomologicalComplex.homologyColimitIso (G ⋙ finiteDiagramAt.{t} k A M) n).inv ≫
      HomologicalComplex.homologyMap (stableTraceAt.{t} k A M G) n =
      HomologicalComplex.homologyMap (traceChainMapAt.{t} k A M (Fin (G.obj r + 1))) n := by
    rw [← Category.assoc, HomologicalComplex.ι_comp_homologyColimitIso_inv,
      ← HomologicalComplex.homologyMap_comp, ι_stableTraceAt]
  exact hl.trans hr.symm

/-- The inverse homology comparison is induced by the actual stable corner. -/
theorem stableHomologyIsoAt_inv (G : J ⥤ ℕ) (n : ℕ) :
    (stableHomologyIsoAt.{t} k A M G n).inv =
      HomologicalComplex.homologyMap (stableCornerAt.{t} k A M G) n := by
  rw [← cancel_mono (stableHomologyIsoAt.{t} k A M G n).hom, Iso.inv_hom_id,
    stableHomologyIsoAt_hom, ← HomologicalComplex.homologyMap_comp,
    stableCornerAt_comp_trace, HomologicalComplex.homologyMap_id]

/-- The stable homology comparison is natural in the indexing functor. -/
theorem stableHomologyIsoAt_naturality {G G' : J ⥤ ℕ} (τ : G ⟶ G') (n : ℕ) :
    HomologicalComplex.homologyMap (stableMapAt.{t} k A M τ) n ≫
        (stableHomologyIsoAt.{t} k A M G' n).hom =
      (stableHomologyIsoAt.{t} k A M G n).hom := by
  rw [stableHomologyIsoAt_hom, stableHomologyIsoAt_hom,
    ← HomologicalComplex.homologyMap_comp, stableMapAt_comp_trace]

end ModuleCat.Algebra.Hochschild.Matrix.StableMorita
