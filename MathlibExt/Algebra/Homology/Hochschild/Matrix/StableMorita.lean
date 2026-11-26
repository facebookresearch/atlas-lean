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
# Connected exact colimits of positive-size matrix Hochschild complexes

Let k be a commutative ring, A an associative unital k-algebra and M
a compatible A-bimodule. At H=max(u,v,w,t), the diagram
D(r)=C_*(Mat_(r+1)(A),ULift^H Mat_(r+1)(M)), r∈ℕ,
has transitions given by top-left zero extension. Its traces form a
natural map to the constant coefficient complex C=C_*(A,ULift^H M),
and its corners at matrix index zero form a natural map in reverse.

For a category J and G:J→ℕ, form S_G=colim_J(G⋙D), assuming colimits
of shape J in ModuleCat^H(k). If J is connected, the compatible
corners give I_G:C→S_G, and the trace T_G:S_G→C satisfies T_G I_G=id.
If those colimits are also exact, trace induces H_n(S_G)≅H_n(C),
with inverse H_n(I_G), for every n≥0.

The homology isomorphism is natural for transformations G→G′.
The object and morphism worlds of J are independent of k,A,M and H;
no relation between those worlds is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MulOpposite
open scoped BigOperators TensorProduct

universe t u v w j j'

namespace ModuleCat.Algebra.Hochschild.Matrix.StableMorita

section ConnectedConstants

universe c

private instance (priority := 2000) connectedConstantModuleHasColimit
    {k : Type u} [CommRing k] {J : Type j} [Category.{j'} J] [IsConnected J]
    (X : ModuleCat.{c} k) : HasColimit ((Functor.const J).obj X) :=
  hasColimit_const_of_isConnected (J := J) (C := ModuleCat.{c} k) X

private instance (priority := 2000) connectedConstantChainHasColimit
    {k : Type u} [CommRing k] {J : Type j} [Category.{j'} J] [IsConnected J]
    (X : ChainComplex (ModuleCat.{c} k) ℕ) : HasColimit ((Functor.const J).obj X) :=
  hasColimit_const_of_isConnected
    (J := J) (C := ChainComplex (ModuleCat.{c} k) ℕ) X

end ConnectedConstants

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

/-- For k-modules M,A and r≤s, extending a coefficient matrix
and all n algebra matrices by zero from size r to size s preserves
the generalized trace. As k-linear maps,
T_n^s ∘ (Z_M ⊗ Z_A^⊗n) = T_n^r, including r=0. -/
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

/-- For a left A-module M and r≤s, top-left zero extension
satisfies Z(B) • Z(X) = Z(B • X), for B∈Mat_r(A) and
X∈Mat_r(M), with the left matrix action.
The entry formula is (B • X)ᵢⱼ=∑ₚ Bᵢₚ • Xₚⱼ. -/
theorem zeroExtend_left {r s : ℕ} (h : r ≤ s)
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

/-- For a right A-module M and r≤s, top-left zero extension
satisfies op(Z(B)) • Z(X) = Z(op(B) • X), for B∈Mat_r(A)
and X∈Mat_r(M). The entry formula is
(op B • X)ᵢⱼ=∑ₚ op(Bₚⱼ) • Xᵢₚ. -/
theorem zeroExtend_right {r s : ℕ} (h : r ≤ s)
    (B : Matrix (Fin r) (Fin r) A) (X : Matrix (Fin r) (Fin r) M) :
    op (Matrix.zeroExtend h B) • Matrix.zeroExtend h X = Matrix.zeroExtend h (op B • X) := by
  ext i l
  rw [Coefficients.right_smul_apply]
  simp only [MulOpposite.unop_op]
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
            simp only [Matrix.zeroExtend_apply, hi, hl, hp, ↓reduceDIte,
              MulOpposite.op_zero, smul_zero]
        _ = _ := sum_truncate h (fun p : Fin r => op (B p ⟨l.val, hl⟩) • X ⟨i.val, hi⟩ p)
    · rw [Matrix.zeroExtend_of_col h _ i l (Nat.le_of_not_gt hl)]
      apply Finset.sum_eq_zero
      intro p _
      rw [Matrix.zeroExtend_of_col h B p l (Nat.le_of_not_gt hl),
        MulOpposite.op_zero, zero_smul]
  · rw [Matrix.zeroExtend_of_row h _ i l (Nat.le_of_not_gt hi)]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.zeroExtend_of_row h X i p (Nat.le_of_not_gt hi), smul_zero]

/-- For a k-algebra A and a compatible A-bimodule M,
r≤s gives the chain map D(r)→D(s) by zero extension from
(r+1)×(r+1) to (s+1)×(s+1) matrices.
Both coefficient modules are lifted to H=max(u,v,w,t), and
the algebra map is allowed to be nonunital. -/
def finiteTransitionAt {r s : ℕ} (h : r ≤ s) :
    chainComplex k (Matrix (Fin (r + 1)) (Fin (r + 1)) A)
        (ULift.{max u v w t} (Matrix (Fin (r + 1)) (Fin (r + 1)) M)) ⟶
      chainComplex k (Matrix (Fin (s + 1)) (Fin (s + 1)) A)
        (ULift.{max u v w t} (Matrix (Fin (s + 1)) (Fin (s + 1)) M)) :=
  liftedMapAt.{t} (Matrix.zeroExtendAlgHom (k := k) (A := A) (Nat.succ_le_succ h))
    (Matrix.zeroExtendLinear (k := k) (A := M) (Nat.succ_le_succ h))
    (fun B X => (zeroExtend_left (A := A) (M := M) (Nat.succ_le_succ h) B X).symm)
    (fun B X => (zeroExtend_right (A := A) (M := M) (Nat.succ_le_succ h) B X).symm)

/-- For a k-algebra A, a compatible A-bimodule M and r≤s,
the degree-n transition sends up(X)⊗a₁⊗⋯⊗aₙ to
up(Z(X))⊗Z(a₁)⊗⋯⊗Z(aₙ), with Z the top-left zero
extension between sizes r+1 and s+1.
The common coefficient height is H=max(u,v,w,t). -/
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

/-- For a k-algebra A and a compatible A-bimodule M, the
finite transition at r≤r is id on
C_*(Mat_(r+1)(A),ULift^H Mat_(r+1)(M)).
Here H=max(u,v,w,t). -/
theorem finiteTransitionAt_self (r : ℕ) :
    finiteTransitionAt.{t} k A M (le_rfl : r ≤ r) =
      𝟙 (chainComplex k (Matrix (Fin (r + 1)) (Fin (r + 1)) A)
        (ULift.{max u v w t} (Matrix (Fin (r + 1)) (Fin (r + 1)) M))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro X a
  rcases X with ⟨X⟩
  change ((finiteTransitionAt.{t} k A M (le_rfl : r ≤ r)).f n).hom
    (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a) =
      ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a
  simpa only [Matrix.zeroExtend_self] using
    finiteTransitionAt_f_tprod.{t} k A M (le_rfl : r ≤ r) n X a

/-- For a k-algebra A, a compatible A-bimodule M and r≤s≤q,
the zero-extension chain transitions satisfy
D(s→q) ∘ D(r→s) = D(r→q), at height H=max(u,v,w,t).
They retain the same top-left matrix entries. -/
theorem finiteTransitionAt_comp {r s q : ℕ} (h : r ≤ s) (h' : s ≤ q) :
    finiteTransitionAt.{t} k A M h ≫ finiteTransitionAt.{t} k A M h' =
      finiteTransitionAt.{t} k A M (h.trans h') := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro X a
  rcases X with ⟨X⟩
  change ((finiteTransitionAt.{t} k A M h').f n).hom
      (((finiteTransitionAt.{t} k A M h).f n).hom
        (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    ((finiteTransitionAt.{t} k A M (h.trans h')).f n).hom
      (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [finiteTransitionAt_f_tprod.{t} k A M h n X a,
    finiteTransitionAt_f_tprod.{t} k A M h' n
      (Matrix.zeroExtend (Nat.succ_le_succ h) X)
      (fun i => Matrix.zeroExtend (Nat.succ_le_succ h) (a i)),
    finiteTransitionAt_f_tprod.{t} k A M (h.trans h') n X a]
  simp only [Matrix.zeroExtend_comp]
  rfl

/-- For a k-algebra A and a compatible A-bimodule M, the
functor D:ℕ→ChainComplex(ModuleCat^H(k),ℕ) sends r to
C_*(Mat_(r+1)(A),ULift^H Mat_(r+1)(M)).
Its transitions are top-left zero extensions, and every matrix
size in the diagram is positive. -/
def finiteDiagramAt : ℕ ⥤ ChainComplex (ModuleCat.{max u v w t} k) ℕ where
  obj r := chainComplex k (Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (ULift.{max u v w t} (Matrix (Fin (r + 1)) (Fin (r + 1)) M))
  map h := finiteTransitionAt.{t} k A M (leOfHom h)
  map_id r := finiteTransitionAt_self.{t} k A M r
  map_comp f g := (finiteTransitionAt_comp.{t} k A M (leOfHom f) (leOfHom g)).symm

/-- For a k-algebra A, a compatible A-bimodule M and r≤s,
the traces satisfy T_s ∘ D(r→s) = T_r as chain maps
D(r)→C_*(A,ULift^H M), with H=max(u,v,w,t). -/
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

/-- For a k-algebra A, a compatible A-bimodule M and r≤s,
the corners at index zero satisfy D(r→s) ∘ I_r = I_s.
The corner I_r enters the positive-size matrix complex D(r),
and all coefficient heights are H=max(u,v,w,t). -/
theorem corner_comp_finiteTransitionAt {r s : ℕ} (h : r ≤ s) :
    Morita.cornerChainMapAt.{t} k A M (Fin (r + 1)) 0 ≫ finiteTransitionAt.{t} k A M h =
      Morita.cornerChainMapAt.{t} k A M (Fin (s + 1)) 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro m a
  rcases m with ⟨m⟩
  change ((finiteTransitionAt.{t} k A M h).f n).hom
      (((Morita.cornerChainMapAt.{t} k A M (Fin (r + 1)) 0).f n).hom
        (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    ((Morita.cornerChainMapAt.{t} k A M (Fin (s + 1)) 0).f n).hom
      (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [Morita.cornerChainMapAt_f_tprod.{t} k A M (Fin (r + 1)) 0 n m a,
    finiteTransitionAt_f_tprod.{t} k A M h n
      (cornerLinear k (Fin (r + 1)) 0 m)
      (fun i => cornerLinear k (Fin (r + 1)) 0 (a i)),
    Morita.cornerChainMapAt_f_tprod.{t} k A M (Fin (s + 1)) 0 n m a]
  have hm : Matrix.zeroExtend (Nat.succ_le_succ h)
      (cornerLinear k (Fin (r + 1)) 0 m) = cornerLinear k (Fin (s + 1)) 0 m :=
    zeroExtend_corner (k := k) h m
  have ha : (fun i : Fin n => Matrix.zeroExtend (Nat.succ_le_succ h)
        (cornerLinear k (Fin (r + 1)) 0 (a i))) =
      (fun i : Fin n => cornerLinear k (Fin (s + 1)) 0 (a i)) :=
    funext (fun i => zeroExtend_corner (k := k) h (a i))
  have hcoords :
      (ULift.up (Matrix.zeroExtend (Nat.succ_le_succ h)
        (cornerLinear k (Fin (r + 1)) 0 m)) ⊗ₜ[k]
          PiTensorProduct.tprod k
            (fun i => Matrix.zeroExtend (Nat.succ_le_succ h)
              (cornerLinear k (Fin (r + 1)) 0 (a i))) :
        ULift.{max u v w t} (Matrix (Fin (s + 1)) (Fin (s + 1)) M) ⊗[k]
          TensorPower k n (Matrix (Fin (s + 1)) (Fin (s + 1)) A)) =
      ULift.up (cornerLinear k (Fin (s + 1)) 0 m) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i => cornerLinear k (Fin (s + 1)) 0 (a i)) :=
    congrArg₂ (fun (x : Matrix (Fin (s + 1)) (Fin (s + 1)) M)
        (b : Fin n → Matrix (Fin (s + 1)) (Fin (s + 1)) A) =>
      (ULift.up x : ULift.{max u v w t} (Matrix (Fin (s + 1)) (Fin (s + 1)) M)) ⊗ₜ[k]
        PiTensorProduct.tprod k b) hm ha
  exact hcoords

/-- For a k-algebra A and a compatible A-bimodule M, the
finite trace maps form D→const(C_*(A,ULift^H M)).
The naturality equation is T_s D(r→s)=T_r, with
D(r) the size-(r+1) coefficient complex and H=max(u,v,w,t). -/
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

/-- For a k-algebra A and a compatible A-bimodule M, the
corners at matrix index zero form const(C_*(A,ULift^H M))→D.
Positive-size zero extension preserves these corners in every
degree, at H=max(u,v,w,t). -/
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

/-- For a k-algebra A, a compatible A-bimodule M, a category J,
G:J→ℕ and n≥0, finite trace gives the natural isomorphism
j ↦ H_n(D(Gj)) ≅ const_J(H_n(C_*(A,ULift^H M))).
Its component inverse is the homology map of the zero-index
finite corner; connectedness is not needed for this finite
diagram comparison. -/
def traceHomologyNatIsoAt (G : J ⥤ ℕ) (n : ℕ) :
    (G ⋙ finiteDiagramAt.{t} k A M) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
          (ComplexShape.down ℕ) n ≅
      (Functor.const J).obj ((chainComplex k A (ULift.{max u v w t} M)).homology n) :=
  (show (G ⋙ finiteDiagramAt.{t} k A M) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
          (ComplexShape.down ℕ) n ≅
      (Functor.const J).obj (chainComplex k A (ULift.{max u v w t} M)) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
          (ComplexShape.down ℕ) n from
    HomologicalComplex.homologyNatIsoOfQuasiIsoAt
      (Functor.whiskerLeft G (traceNatAt.{t} k A M)) n (fun r => by
        apply (quasiIsoAt_iff_isIso_homologyMap _ n).2
        exact (Morita.finiteHomologyIsoAt.{t} k A M (Fin (G.obj r + 1)) 0 n).isIso_hom)) ≪≫
    Functor.constComp J
      (chainComplex k A (ULift.{max u v w t} M) :
        ChainComplex (ModuleCat.{max u v w t} k) ℕ)
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
        (ComplexShape.down ℕ) n)

@[simp]
theorem traceHomologyNatIsoAt_hom_app (G : J ⥤ ℕ) (n : ℕ) (r : J) :
    (traceHomologyNatIsoAt.{t} k A M G n).hom.app r =
      HomologicalComplex.homologyMap (traceChainMapAt.{t} k A M (Fin (G.obj r + 1))) n := by
  change HomologicalComplex.homologyMap
      (traceChainMapAt.{t} k A M (Fin (G.obj r + 1))) n ≫ 𝟙 _ = _
  exact Category.comp_id _

variable [HasColimitsOfShape J (ModuleCat.{max u v w t} k)]

/-- For a k-algebra A, a compatible A-bimodule M and G:J→ℕ,
assume colimits of shape J in ModuleCat^H(k), H=max(u,v,w,t).
The colimit model is S_G=colim_J(G⋙D) in chain complexes.
The object and morphism worlds of J remain independent of H. -/
abbrev stableComplexAt (G : J ⥤ ℕ) : ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
  colimit (G ⋙ finiteDiagramAt.{t} k A M)

private def traceCoconeAt (G : J ⥤ ℕ) : Cocone (G ⋙ finiteDiagramAt.{t} k A M) where
  pt := chainComplex k A (ULift.{max u v w t} M)
  ι := Functor.whiskerLeft G (traceNatAt.{t} k A M)

/-- For a k-algebra A, a compatible A-bimodule M and G:J→ℕ
with shape-J colimits in ModuleCat^H(k), the trace
T_G:S_G→C_*(A,ULift^H M) is induced by the compatible finite
traces. Its composite with each colimit leg is the trace at
that positive-size stage. -/
def stableTraceAt (G : J ⥤ ℕ) :
    stableComplexAt.{t} k A M G ⟶ chainComplex k A (ULift.{max u v w t} M) :=
  colimit.desc _
    { pt := chainComplex k A (ULift.{max u v w t} M)
      ι := Functor.whiskerLeft G (traceNatAt.{t} k A M) }

@[reassoc]
theorem ι_stableTraceAt (G : J ⥤ ℕ) (r : J) :
    colimit.ι (G ⋙ finiteDiagramAt.{t} k A M) r ≫ stableTraceAt.{t} k A M G =
      traceChainMapAt.{t} k A M (Fin (G.obj r + 1)) := by
  exact colimit.ι_desc (traceCoconeAt.{t} k A M G) r

/-- For a k-algebra A, a compatible A-bimodule M and a
transformation τ:G→G′ between functors J→ℕ, the finite
size transitions induce S_G→S_G′ by the colimit universal property.
The two complexes use the same shape-J colimits and height
H=max(u,v,w,t). -/
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
    colimit ((Functor.const J).obj
      (chainComplex k A (ULift.{max u v w t} M) :
        ChainComplex (ModuleCat.{max u v w t} k) ℕ)) ≅
      (chainComplex k A (ULift.{max u v w t} M) :
        ChainComplex (ModuleCat.{max u v w t} k) ℕ) :=
  let X : ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
    chainComplex k A (ULift.{max u v w t} M)
  let c : ColimitCocone ((Functor.const J).obj X) :=
    ⟨constCocone J X, isColimitConstCocone J X⟩
  colimit.isoColimitCocone c

private theorem constantColimitIsoAt_leg (r : J) :
    colimit.ι ((Functor.const J).obj
      (chainComplex k A (ULift.{max u v w t} M) :
        ChainComplex (ModuleCat.{max u v w t} k) ℕ)) r ≫
        (constantColimitIsoAt.{t} (J := J) k A M).hom =
      𝟙 (chainComplex k A (ULift.{max u v w t} M)) :=
  colimit.isoColimitCocone_ι_hom
    (show ColimitCocone ((Functor.const J).obj
      (chainComplex k A (ULift.{max u v w t} M) :
        ChainComplex (ModuleCat.{max u v w t} k) ℕ)) from
      ⟨constCocone J (chainComplex k A (ULift.{max u v w t} M) :
          ChainComplex (ModuleCat.{max u v w t} k) ℕ),
        isColimitConstCocone J (chainComplex k A (ULift.{max u v w t} M) :
          ChainComplex (ModuleCat.{max u v w t} k) ℕ)⟩) r

private theorem constantColimitIsoAt_inv_eq_ι (r : J) :
    (constantColimitIsoAt.{t} (J := J) k A M).inv =
      colimit.ι ((Functor.const J).obj
        (chainComplex k A (ULift.{max u v w t} M) :
          ChainComplex (ModuleCat.{max u v w t} k) ℕ)) r := by
  apply (cancel_mono (constantColimitIsoAt.{t} (J := J) k A M).hom).mp
  rw [Iso.inv_hom_id, constantColimitIsoAt_leg]

/-- For a k-algebra A, a compatible A-bimodule M and
G:J→ℕ, assume J connected and shape-J colimits in
ModuleCat^H(k). The compatible zero-index corners define
I_G:C_*(A,ULift^H M)→S_G through the colimit of the constant
coefficient complex. Here H=max(u,v,w,t). -/
def stableCornerAt (G : J ⥤ ℕ) :
    chainComplex k A (ULift.{max u v w t} M) ⟶ stableComplexAt.{t} k A M G :=
  let X : ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
    chainComplex k A (ULift.{max u v w t} M)
  let c : ColimitCocone ((Functor.const J).obj X) :=
    ⟨constCocone J X, isColimitConstCocone J X⟩
  (colimit.isoColimitCocone c).inv ≫
    colimMap (Functor.whiskerLeft G (cornerNatAt.{t} k A M))

/-- For connected J, G:J→ℕ and shape-J colimits at
H=max(u,v,w,t), the stable corner equals the zero-index corner
into D(Gr) followed by the colimit leg, for every r∈J.
The algebra A and compatible bimodule M have independent
carrier worlds. -/
theorem stableCornerAt_eq_stage (G : J ⥤ ℕ) (r : J) :
    stableCornerAt.{t} k A M G =
      Morita.cornerChainMapAt.{t} k A M (Fin (G.obj r + 1)) 0 ≫
        colimit.ι (G ⋙ finiteDiagramAt.{t} k A M) r := by
  let X : ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
    chainComplex k A (ULift.{max u v w t} M)
  let F : J ⥤ ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
    (Functor.const J).obj X
  let K : J ⥤ ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
    G ⋙ finiteDiagramAt.{t} k A M
  let τ : F ⟶ K := Functor.whiskerLeft G (cornerNatAt.{t} k A M)
  let c : ColimitCocone F := ⟨constCocone J X, isColimitConstCocone J X⟩
  let e : colimit F ≅ X := colimit.isoColimitCocone c
  have he : e.inv = colimit.ι F r := by
    apply (cancel_mono e.hom).mp
    calc
      e.inv ≫ e.hom = 𝟙 X := e.inv_hom_id
      _ = colimit.ι F r ≫ e.hom := by
        symm
        exact colimit.isoColimitCocone_ι_hom c r
  change e.inv ≫ colimMap τ = τ.app r ≫ colimit.ι K r
  rw [he]
  simpa only [colimMap_eq] using ι_colimMap τ r

/-- For a k-algebra A, a compatible A-bimodule M, connected J
and G:J→ℕ with shape-J colimits at H=max(u,v,w,t),
the stable maps satisfy T_G ∘ I_G = id on
C_*(A,ULift^H M) as chain maps. -/
theorem stableCornerAt_comp_trace (G : J ⥤ ℕ) :
    stableCornerAt.{t} k A M G ≫ stableTraceAt.{t} k A M G =
      𝟙 (chainComplex k A (ULift.{max u v w t} M)) := by
  let r : J := Classical.arbitrary J
  rw [stableCornerAt_eq_stage k A M G r]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => Morita.cornerChainMapAt.{t} k A M (Fin (G.obj r + 1)) 0 ≫ f)
      (ι_stableTraceAt.{t} k A M G r)).trans
        (Morita.cornerChainMapAt_comp_trace.{t} k A M (Fin (G.obj r + 1)) 0))

variable [HasExactColimitsOfShape J (ModuleCat.{max u v w t} k)]

/-- For a k-algebra A, a compatible A-bimodule M and G:J→ℕ,
assume J connected and both shape-J colimits and exact
shape-J colimits in ModuleCat^H(k), H=max(u,v,w,t).
Then H_n(S_G) ≅ H_n(C_*(A,ULift^H M)) for every n≥0,
with maps induced by the actual colimit trace and stable corner.
The category-index worlds are independent of H. -/
def stableHomologyIsoAt (G : J ⥤ ℕ) (n : ℕ) :
    (stableComplexAt.{t} k A M G).homology n ≅
      (chainComplex k A (ULift.{max u v w t} M)).homology n :=
  let K : J ⥤ ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
    G ⋙ finiteDiagramAt.{t} k A M
  let H : ChainComplex (ModuleCat.{max u v w t} k) ℕ ⥤
      ModuleCat.{max u v w t} k :=
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
      (ComplexShape.down ℕ) n
  let X : ModuleCat.{max u v w t} k :=
    H.obj (chainComplex k A (ULift.{max u v w t} M))
  let e : K ⋙ H ≅ (Functor.const J).obj X := traceHomologyNatIsoAt.{t} k A M G n
  let c : ColimitCocone ((Functor.const J).obj X) :=
    ⟨constCocone J X, isColimitConstCocone J X⟩
  letI : HasColimit (K ⋙ H) :=
    HasColimitsOfShape.has_colimit (J := J) (C := ModuleCat.{max u v w t} k) (K ⋙ H)
  letI : HasColimit ((Functor.const J).obj X) := HasColimit.mk c
  letI : PreservesFiniteLimits (colim (J := J) (C := ModuleCat.{max u v w t} k)) :=
    HasExactColimitsOfShape.preservesFiniteLimits (J := J) (C := ModuleCat.{max u v w t} k)
  letI : (colim (J := J) (C := ModuleCat.{max u v w t} k)).PreservesHomology :=
    Functor.preservesHomologyOfExact (colim (J := J) (C := ModuleCat.{max u v w t} k))
  HomologicalComplex.homologyColimitIso (C := ModuleCat.{max u v w t} k)
      K n ≪≫ HasColimit.isoOfNatIso e ≪≫
    colimit.isoColimitCocone c

/-- Under connectedness of J and exact shape-J colimits in
ModuleCat^H(k), the isomorphism H_n(S_G)≅H_n(C_*(A,ULift^H M))
has forward morphism H_n(T_G).
Here G:J→ℕ, A is a k-algebra, M a compatible A-bimodule and
H=max(u,v,w,t). -/
theorem stableHomologyIsoAt_hom (G : J ⥤ ℕ) (n : ℕ) :
    (stableHomologyIsoAt.{t} k A M G n).hom =
      HomologicalComplex.homologyMap (stableTraceAt.{t} k A M G) n := by
  let K : J ⥤ ChainComplex (ModuleCat.{max u v w t} k) ℕ :=
    G ⋙ finiteDiagramAt.{t} k A M
  let H : ChainComplex (ModuleCat.{max u v w t} k) ℕ ⥤
      ModuleCat.{max u v w t} k :=
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v w t} k)
      (ComplexShape.down ℕ) n
  let X : ModuleCat.{max u v w t} k :=
    H.obj (chainComplex k A (ULift.{max u v w t} M))
  let e : K ⋙ H ≅ (Functor.const J).obj X := traceHomologyNatIsoAt.{t} k A M G n
  let c : ColimitCocone ((Functor.const J).obj X) :=
    ⟨constCocone J X, isColimitConstCocone J X⟩
  letI : HasColimit (K ⋙ H) :=
    HasColimitsOfShape.has_colimit (J := J) (C := ModuleCat.{max u v w t} k) (K ⋙ H)
  letI : HasColimit ((Functor.const J).obj X) := HasColimit.mk c
  letI : PreservesFiniteLimits (colim (J := J) (C := ModuleCat.{max u v w t} k)) :=
    HasExactColimitsOfShape.preservesFiniteLimits (J := J) (C := ModuleCat.{max u v w t} k)
  letI : (colim (J := J) (C := ModuleCat.{max u v w t} k)).PreservesHomology :=
    Functor.preservesHomologyOfExact (colim (J := J) (C := ModuleCat.{max u v w t} k))
  change (HomologicalComplex.homologyColimitIso (C := ModuleCat.{max u v w t} k) K n ≪≫
       HasColimit.isoOfNatIso e ≪≫ colimit.isoColimitCocone c).hom = _
  apply (cancel_epi (HomologicalComplex.homologyColimitIso
    (C := ModuleCat.{max u v w t} k) K n).inv).1
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
  apply colimit.hom_ext
  intro r
  have hl : colimit.ι (K ⋙ H) r ≫ (HasColimit.isoOfNatIso e).hom ≫
      (colimit.isoColimitCocone c).hom =
      HomologicalComplex.homologyMap (traceChainMapAt.{t} k A M (Fin (G.obj r + 1))) n := by
     rw [HasColimit.ι_isoOfNatIso_hom_assoc,
       colimit.isoColimitCocone_ι_hom, constCocone_ι, NatTrans.id_app, Category.comp_id]
     exact traceHomologyNatIsoAt_hom_app.{t} k A M G n r
  have hr : colimit.ι (K ⋙ H) r ≫
      (HomologicalComplex.homologyColimitIso (C := ModuleCat.{max u v w t} k) K n).inv ≫
      HomologicalComplex.homologyMap (stableTraceAt.{t} k A M G) n =
      HomologicalComplex.homologyMap (traceChainMapAt.{t} k A M (Fin (G.obj r + 1))) n := by
    rw [← Category.assoc, HomologicalComplex.ι_comp_homologyColimitIso_inv]
    change HomologicalComplex.homologyMap (colimit.ι K r) n ≫
      HomologicalComplex.homologyMap (stableTraceAt.{t} k A M G) n = _
    rw [← HomologicalComplex.homologyMap_comp, ι_stableTraceAt]
    rfl
  exact hl.trans hr.symm

/-- For a k-algebra A, a compatible A-bimodule M and
G:J→ℕ with connected exact shape-J colimits at height
H=max(u,v,w,t), the inverse of the stable homology comparison
is H_n(I_G):H_n(C_*(A,ULift^H M))→H_n(S_G). -/
theorem stableHomologyIsoAt_inv (G : J ⥤ ℕ) (n : ℕ) :
    (stableHomologyIsoAt.{t} k A M G n).inv =
      HomologicalComplex.homologyMap (stableCornerAt.{t} k A M G) n := by
  apply (cancel_mono (stableHomologyIsoAt.{t} k A M G n).hom).1
  rw [Iso.inv_hom_id,
    stableHomologyIsoAt_hom, ← HomologicalComplex.homologyMap_comp,
    stableCornerAt_comp_trace, HomologicalComplex.homologyMap_id]

/-- For a k-algebra A, a compatible A-bimodule M, connected J
with exact shape-J colimits at H=max(u,v,w,t), and τ:G→G′,
the homology comparisons satisfy
χ_G′ ∘ H_n(S(τ)) = χ_G, for every n≥0.
The target is the same coefficient homology H_n(C_*(A,ULift^H M)). -/
theorem stableHomologyIsoAt_naturality {G G' : J ⥤ ℕ} (τ : G ⟶ G') (n : ℕ) :
    HomologicalComplex.homologyMap (stableMapAt.{t} k A M τ) n ≫
        (stableHomologyIsoAt.{t} k A M G' n).hom =
      (stableHomologyIsoAt.{t} k A M G n).hom := by
  rw [stableHomologyIsoAt_hom, stableHomologyIsoAt_hom,
    ← HomologicalComplex.homologyMap_comp, stableMapAt_comp_trace]

end ModuleCat.Algebra.Hochschild.Matrix.StableMorita
