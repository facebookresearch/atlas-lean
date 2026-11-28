/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.Basis.FiniteFiltration
public import MathlibExt.LinearAlgebra.Determinant.FiniteFiltration

/-!
# Determinant one from a filtration-unipotent basis condition

Let R be a commutative ring and 0=F_0⊆⋯⊆F_n a finite filtration in M, with quotient bases b_i
indexed by κ_i. Write B for the assembled basis whose grade-i vector represents b_i in
F_(i+1)/F_i. Assume F_n=M. Suppose every κ_i is finite and U(B_(i,a))-B_(i,a)∈F_i for each
grade and basis index. Then all stages are U-invariant, every graded quotient action is the
identity, and det(U)=1.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Module
open scoped BigOperators

universe uR uM uι

namespace Module.Basis

variable {R : Type uR} {M : Type uM} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable {κ : ℕ → Type uι}

/-- **Earlier stage-basis vectors retain their ambient values.**

Let R be a commutative ring and 0=F_0⊆⋯⊆F_n a finite filtration in M, with quotient bases b_i
indexed by κ_i. Write B for the assembled basis whose grade-i vector represents b_i in
F_(i+1)/F_i. For j≤n and i<j, the grade-i vector assembled in F_j equals its counterpart
assembled in F_n as an element of M. F_n need not equal M for this stage comparison.
-/
private theorem coe_ofFiltrationStage_eq_of_le
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    {j : ℕ} (hj : j ≤ n) (i : Fin j) (a : κ i.val) :
    ((ofFiltrationStage F hzero κ j
        (fun k => hF (k.castLE hj))
        (fun k => b (k.castLE hj)) ⟨i, a⟩ : F j) : M) =
      ((ofFiltrationStage F hzero κ n hF b
        ⟨i.castLE hj, a⟩ : F n) : M) := by
  induction n with
  | zero => exact Fin.elim0 (i.castLE hj)
  | succ n ih =>
      by_cases hjn : j ≤ n
      · calc
          _ = ((ofFiltrationStage F hzero κ n
                (fun k => hF k.castSucc)
                (fun k => b k.castSucc)
                ⟨i.castLE hjn, a⟩ : F n) : M) :=
            ih (fun k => hF k.castSucc) (fun k => b k.castSucc) hjn
          _ = ((ofFiltrationStage F hzero κ (n + 1) hF b
                ⟨i.castLE hj, a⟩ : F (n + 1)) : M) := by
            symm
            simpa using ofFiltrationStage_castSucc F hzero κ n hF b
              (i.castLE hjn) a
      · have hjeq : j = n + 1 := by omega
        subst j
        rfl

private theorem filtration_mono_of_succ
    (F : ℕ → Submodule R M) (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : F i ≤ F j := by
  revert hj
  refine Nat.le_induction (m := i)
    (motive := fun j _ => j ≤ n → F i ≤ F j) ?_ ?_ j hij
  · intro _
    exact le_rfl
  · intro k hik ih hk1n
    exact (ih (Nat.le_trans (Nat.le_succ k) hk1n)).trans
      (hF ⟨k, Nat.lt_of_succ_le hk1n⟩)

/-- **Prefix stage basis equals the corresponding final ambient basis.**

Let R be a commutative ring and 0=F_0⊆⋯⊆F_n a finite filtration in M, with quotient bases b_i
indexed by κ_i. Write B for the assembled basis whose grade-i vector represents b_i in
F_(i+1)/F_i. Assume F_n=M. For j≤n and i<j, the vector of the assembled ambient basis at (i,a)
equals the stage-F_j vector with the same graded index.
-/
theorem ofFiltration_apply_eq_ofFiltrationStage
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤)
    {j : ℕ} (hj : j ≤ n) (i : Fin j) (a : κ i.val) :
    ofFiltration F hzero κ n hF b htop ⟨i.castLE hj, a⟩ =
      ((ofFiltrationStage F hzero κ j
        (fun k => hF (k.castLE hj))
        (fun k => b (k.castLE hj)) ⟨i, a⟩ : F j) : M) := by
  rw [ofFiltration_apply]
  exact (coe_ofFiltrationStage_eq_of_le F hzero n hF b hj i a).symm

/-- **Basis-level lower-stage errors force stage invariance.**

Let R be a commutative ring and 0=F_0⊆⋯⊆F_n a finite filtration in M, with quotient bases b_i
indexed by κ_i. Write B for the assembled basis whose grade-i vector represents b_i in
F_(i+1)/F_i. Assume F_n=M. If U(B_(i,a))-B_(i,a)∈F_i for all i,a, then U(F_j)⊆F_j for every
j≤n. The graded index sets κ_i may be finite or infinite.
-/
theorem ofFiltration_stable
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤)
    (U : M →ₗ[R] M)
    (hU : ∀ i : Fin n, ∀ a : κ i.val,
      U (ofFiltration F hzero κ n hF b htop ⟨i, a⟩) -
          ofFiltration F hzero κ n hF b htop ⟨i, a⟩ ∈ F i.val)
    (j : ℕ) (hj : j ≤ n) : F j ≤ (F j).comap U := by
  let bj := ofFiltrationStage F hzero κ j
    (fun k => hF (k.castLE hj)) (fun k => b (k.castLE hj))
  have hspan :
      Submodule.span R ((F j).subtype '' Set.range bj) = F j := by
    rw [← Submodule.map_span, bj.span_eq, Submodule.map_subtype_top]
  calc
    F j = Submodule.span R ((F j).subtype '' Set.range bj) := hspan.symm
    _ ≤ (F j).comap U := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, ⟨p, rfl⟩, rfl⟩
      change U (bj p : M) ∈ F j
      have hpref := ofFiltration_apply_eq_ofFiltrationStage
        F hzero n hF b htop hj p.1 p.2
      have herr := hU (p.1.castLE hj) p.2
      rw [hpref] at herr
      have herrj : U (bj p : M) - (bj p : M) ∈ F j :=
        filtration_mono_of_succ F n hF (Nat.le_of_lt p.1.isLt) hj herr
      rw [← sub_add_cancel (U (bj p : M)) (bj p : M)]
      exact Submodule.add_mem _ herrj (bj p).property

end Module.Basis

namespace LinearMap

open Module.Basis

variable {R : Type uR} {M : Type uM} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable {κ : ℕ → Type uι}

/-- **Filtration-unipotent endomorphism has determinant one.**

Let R be a commutative ring and 0=F_0⊆⋯⊆F_n a finite filtration in M, with quotient bases b_i
indexed by κ_i. Write B for the assembled basis whose grade-i vector represents b_i in
F_(i+1)/F_i. Assume F_n=M. If every κ_i is finite and U(B_(i,a))-B_(i,a)∈F_i for all i,a, then
det(U)=1, including n=0.
-/
theorem det_eq_one_of_sub_mem_ofFiltration
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤)
    (U : M →ₗ[R] M)
    (hU : ∀ i : Fin n, ∀ a : κ i.val,
      U (ofFiltration F hzero κ n hF b htop ⟨i, a⟩) -
          ofFiltration F hzero κ n hF b htop ⟨i, a⟩ ∈ F i.val)
    [∀ i : Fin n, Finite (κ i.val)] :
    U.det = 1 := by
  let _ : ∀ i : Fin n, Fintype (κ i.val) := fun _ => Fintype.ofFinite _
  let B := ofFiltration F hzero κ n hF b htop
  let _ : Module.Free R M := Module.Free.of_basis B
  let _ : Module.Finite R M := Module.Finite.of_basis B
  let stageLE : ∀ j : Fin (n + 1), j.val ≤ n := fun j =>
    Nat.lt_succ_iff.mp j.isLt
  let stageBasis (j : Fin (n + 1)) :
      Basis (FiltrationIndex κ j.val) R (F j.val) :=
    ofFiltrationStage F hzero κ j.val
      (fun k => hF (k.castLE (stageLE j)))
      (fun k => b (k.castLE (stageLE j)))
  let _ : ∀ j : Fin (n + 1), Fintype (FiltrationIndex κ j.val) := fun j => by
    let _ : ∀ i : Fin j.val, Fintype (κ i.val) := fun i =>
      inferInstanceAs (Fintype (κ (i.castLE (stageLE j)).val))
    infer_instance
  let _ : ∀ j : Fin (n + 1), Module.Free R (F j.val) := fun j =>
    Module.Free.of_basis (stageBasis j)
  let _ : ∀ j : Fin (n + 1), Module.Finite R (F j.val) := fun j =>
    Module.Finite.of_basis (stageBasis j)
  let stable (j : Fin (n + 1)) : F j.val ≤ (F j.val).comap U :=
    ofFiltration_stable F hzero n hF b htop U hU j.val (stageLE j)
  let endomorphism (j : Fin (n + 1)) : F j.val →ₗ[R] F j.val :=
    U.restrict (stable j)
  let step (i : Fin n) :
      InvariantExtension (endomorphism i.castSucc) (endomorphism i.succ) :=
    { submodule := (F i.val).comap (F (i.val + 1)).subtype
      stable := by
        intro x hx
        change U (x : M) ∈ F i.val
        exact stable i.castSucc hx
      equiv := (Submodule.comapSubtypeEquivOfLe (hF i)).symm
      intertwines := by
        apply LinearMap.ext
        intro x
        rfl }
  have hquotient (i : Fin n) :
      (step i).quotientMap = LinearMap.id := by
    apply (b i).ext
    intro a
    rw [← ofFiltrationStageVector_mk F hzero κ n hF b i a]
    rw [InvariantExtension.quotientMap_mk]
    apply (Submodule.Quotient.eq _).mpr
    change U
        ((ofFiltrationStageVector F hzero κ n hF b i a : F (i.val + 1)) : M) -
      ((ofFiltrationStageVector F hzero κ n hF b i a : F (i.val + 1)) : M) ∈
        F i.val
    simpa only [ofFiltrationStageVector, ofFiltration_apply] using hU i a
  let _ : Subsingleton (F (0 : Fin (n + 1)).val) := by
    change Subsingleton (F 0)
    rw [hzero]
    infer_instance
  have hdetStage : (endomorphism (Fin.last n)).det = 1 := by
    rw [det_eq_prod_graded_of_bottom_subsingleton
      endomorphism step (fun i => Module.Free.of_basis (b i))]
    simp only [hquotient, LinearMap.det_id, Finset.prod_const_one]
  let eTop : F n ≃ₗ[R] M :=
    (LinearEquiv.ofEq (F n) ⊤ htop).trans Submodule.topEquiv
  have hconj : eTop.conj (endomorphism (Fin.last n)) = U := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := eTop.surjective x
    rfl
  calc
    U.det = (eTop.conj (endomorphism (Fin.last n))).det := by rw [hconj]
    _ = (endomorphism (Fin.last n)).det := by
      change LinearMap.det
          (((eTop : F n →ₗ[R] M) ∘ₗ endomorphism (Fin.last n)) ∘ₗ
            (eTop.symm : M →ₗ[R] F n)) =
        LinearMap.det (endomorphism (Fin.last n))
      exact LinearMap.det_conj (endomorphism (Fin.last n)) eTop
    _ = 1 := hdetStage

/-- **Stagewise lower errors give determinant one.**

Let R be a commutative ring and 0=F_0⊆⋯⊆F_n=M a finite filtration, with a basis b_i indexed by
finite κ_i for each quotient F_(i+1)/F_i. If U x-x belongs to F_i for every x∈F_(i+1), then
det(U)=1. The hypothesis concerns every stage vector and does not depend on chosen lifts.
-/
theorem det_eq_one_of_sub_mem_ofFiltrationStage
    (F : ℕ → Submodule R M) (hzero : F 0 = ⊥)
    (n : ℕ)
    (hF : ∀ i : Fin n, F i.val ≤ F (i.val + 1))
    (b : ∀ i : Fin n,
      Basis (κ i.val) R
        (F (i.val + 1) ⧸ (F i.val).comap (F (i.val + 1)).subtype))
    (htop : F n = ⊤)
    (U : M →ₗ[R] M)
    (hU : ∀ i : Fin n, ∀ x : M,
      x ∈ F (i.val + 1) → U x - x ∈ F i.val)
    [∀ i : Fin n, Finite (κ i.val)] :
    U.det = 1 := by
  apply det_eq_one_of_sub_mem_ofFiltration F hzero n hF b htop U
  intro i a
  apply hU i
  simpa only [ofFiltration_apply] using
    ofFiltrationStage_mem F hzero κ n hF b i a

end LinearMap

end
