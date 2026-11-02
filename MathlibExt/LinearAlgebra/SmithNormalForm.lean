/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/LinearAlgebra/FreeModule/PID.lean` (Mathlib):
Copyright (c) 2020 Anne Baanen. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Anne Baanen
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

namespace MathlibExt.LinearAlgebra.SmithNormalFormWanted

/-- The generator of a maximal coordinate image divides every coordinate value on `N`.
This strengthens `generator_maximal_submoduleImage_dvd` (which only handles the
witness element `y`) to all of `N`, by translating an arbitrary `x` to one with
maximal coordinate value. -/
private theorem aux_generator_dvd_all {R W : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup W] [Module R W]
    {M N : Submodule R W} (hNM : N ≤ M)
    {ϕ : ↥M →ₗ[R] R}
    (hϕ : ∀ ψ : ↥M →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    [((ϕ.submoduleImage N)).IsPrincipal]
    (y : W) (yN : y ∈ N)
    (ϕy_eq : ϕ ⟨y, hNM yN⟩ = Submodule.IsPrincipal.generator (ϕ.submoduleImage N)) :
    ∀ (x : ↥N) (ψ : ↥M →ₗ[R] R),
      Submodule.IsPrincipal.generator (ϕ.submoduleImage N) ∣ ψ ⟨(x : W), hNM x.2⟩ := by
  intro x ψ
  have hb : Submodule.IsPrincipal.generator (ϕ.submoduleImage N) ∣ ϕ ⟨(x : W), hNM x.2⟩ :=
    Submodule.IsPrincipal.generator_submoduleImage_dvd_of_mem hNM ϕ x.2
  obtain ⟨t, ht⟩ := hb
  let Y : ↥M := ⟨y, hNM yN⟩
  let X : ↥M := ⟨(x : W), hNM x.2⟩
  let X' : ↥M := X - t • Y + Y
  have hX'N : (X' : W) ∈ N := by
    change (x : W) - t • y + y ∈ N
    exact Submodule.add_mem _ (Submodule.sub_mem _ x.2 (Submodule.smul_mem _ _ yN)) yN
  have hX' : X' = X - t • Y + Y := rfl
  have hϕX' : ϕ ⟨(X' : W), hNM hX'N⟩ =
      Submodule.IsPrincipal.generator (ϕ.submoduleImage N) := by
    have hval : (⟨(X' : W), hNM hX'N⟩ : ↥M) = X' := Subtype.ext rfl
    rw [hval, hX']
    simp only [map_sub, map_add, map_smul]
    change ϕ X - t • ϕ Y + ϕ Y = _
    have hY : ϕ Y = Submodule.IsPrincipal.generator (ϕ.submoduleImage N) := ϕy_eq
    have hX : ϕ X = Submodule.IsPrincipal.generator (ϕ.submoduleImage N) * t := ht
    rw [hY, hX, smul_eq_mul, mul_comm t _]
    rw [sub_self, zero_add]
  have h1 : Submodule.IsPrincipal.generator (ϕ.submoduleImage N) ∣ ψ ⟨(X' : W), hNM hX'N⟩ :=
    generator_maximal_submoduleImage_dvd hNM hϕ _ hX'N hϕX' ψ
  have h2 : Submodule.IsPrincipal.generator (ϕ.submoduleImage N) ∣ ψ Y :=
    generator_maximal_submoduleImage_dvd hNM hϕ y yN ϕy_eq ψ
  have hXX' : X = X' + t • Y - Y := by rw [hX']; abel
  have hvalX : (⟨(x : W), hNM x.2⟩ : ↥M) = X := rfl
  have hvalX' : (⟨(X' : W), hNM hX'N⟩ : ↥M) = X' := Subtype.ext rfl
  rw [hvalX]
  have hψ : ψ X = ψ X' + (t * ψ Y - ψ Y) := by
    conv_lhs => rw [hXX']
    rw [map_sub, map_add, map_smul, smul_eq_mul, add_sub_assoc]
  rw [hψ]
  exact h1.add ((dvd_mul_of_dvd_right h2 t).sub h2)

/-- Strengthened copy of `Submodule.basis_of_pid_aux`: additionally the chosen scalar
`a` is nonzero, the extension scalars are `Fin.cons`-shaped, the extended basis of `M`
extends the basis of `M'`, and `a` divides every coordinate value on `N`. -/
private theorem aux_basis_of_pid {ι : Type*} {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
    [IsDomain R] [Finite ι] {O : Type*} [AddCommGroup O] [Module R O]
    (M N : Submodule R O) (b'M : Module.Basis ι R M) (N_bot : N ≠ ⊥) (N_le_M : N ≤ M) :
    ∃ y ∈ M, ∃ a : R, a ≠ 0 ∧ a • y ∈ N ∧ ∃ M' ≤ M, ∃ N' ≤ N,
      N' ≤ M' ∧ (∀ (c : R) (z : O), z ∈ M' → c • y + z = 0 → c = 0) ∧
      (∀ (c : R) (z : O), z ∈ N' → c • a • y + z = 0 → c = 0) ∧
      (∀ (n') (bN' : Module.Basis (Fin n') R N'),
        ∃ bN : Module.Basis (Fin (n' + 1)) R N,
          ∀ (m') (hn'm' : n' ≤ m') (bM' : Module.Basis (Fin m') R M'),
            ∃ (hnm : n' + 1 ≤ m' + 1) (bM : Module.Basis (Fin (m' + 1)) R M),
              ((∀ as : Fin n' → R,
                (∀ i : Fin n', (bN' i : O) = as i • (bM' (Fin.castLE hn'm' i) : O)) →
                  ∃ as' : Fin (n' + 1) → R,
                    (∀ i : Fin (n' + 1), (bN i : O) = as' i • (bM (Fin.castLE hnm i) : O)) ∧
                    as' 0 = a ∧ ∀ (i : Fin n'), as' i.succ = as i) ∧
              (∀ (j : Fin m'), (bM j.succ : O) = (bM' j : O)))) ∧
      (∀ (x : ↥N) (Ψ : ↥M →ₗ[R] R),
        a ∣ Ψ ⟨(x : O), N_le_M x.2⟩) := by
  have : ∃ ϕ : M →ₗ[R] R, ∀ ψ : M →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N := by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _
        (show (Set.range fun ψ : M →ₗ[R] R ↦ ψ.submoduleImage N).Nonempty from
          ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩)
    obtain ⟨ϕ, rfl⟩ := Set.mem_range.mp P_eq
    exact ⟨ϕ, fun ψ hψ ↦ P_max _ ⟨_, rfl⟩ hψ⟩
  let ϕ := this.choose
  have ϕ_max := this.choose_spec
  let a := Submodule.IsPrincipal.generator (ϕ.submoduleImage N)
  have a_mem : a ∈ ϕ.submoduleImage N := Submodule.IsPrincipal.generator_mem _
  by_cases a_zero : a = 0
  · have := eq_bot_of_generator_maximal_submoduleImage_eq_zero b'M N_le_M ϕ_max a_zero
    contradiction
  obtain ⟨y, yN, ϕy_eq⟩ := (LinearMap.mem_submoduleImage_of_le N_le_M).mp a_mem
  have hdvd : ∀ i, a ∣ b'M.coord i ⟨y, N_le_M yN⟩ := fun i ↦
    generator_maximal_submoduleImage_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i)
  choose c hc using hdvd
  cases nonempty_fintype ι
  let y' : O := ∑ i, c i • b'M i
  have y'M : y' ∈ M := M.sum_mem fun i _ ↦ M.smul_mem (c i) (b'M i).2
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M i :=
    Subtype.ext
      (show y' = M.subtype _ by
        simp only [map_sum, map_smul]
        rfl)
  have a_smul_y' : a • y' = y := by
    refine Subtype.mk_eq_mk.mp (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩ from ?_)
    rw [← b'M.sum_repr ⟨y, N_le_M yN⟩, mk_y', Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_smul, ← hc]
    rfl
  refine ⟨y', y'M, a, a_zero, a_smul_y'.symm ▸ yN, ?_⟩
  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 :=
    mul_left_cancel₀ a_zero
      (calc
        a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', _⟩ := (ϕ.map_smul a ⟨y', y'M⟩).symm
        _ = ϕ ⟨y, N_le_M yN⟩ := by simp only [a_smul_y']
        _ = a := ϕy_eq
        _ = a * 1 := (mul_one a).symm)
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ ≠ 0 := by simpa only [ϕy'_eq] using one_ne_zero
  let M' : Submodule R O := (LinearMap.ker ϕ).map M.subtype
  let N' : Submodule R O :=
    (LinearMap.ker (ϕ.comp (Submodule.inclusion N_le_M))).map N.subtype
  have M'_le_M : M' ≤ M := M.map_subtype_le (LinearMap.ker ϕ)
  have N'_le_M' : N' ≤ M' := by
    intro x hx
    simp only [N', Submodule.mem_map, LinearMap.mem_ker] at hx ⊢
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩
  have N'_le_N : N' ≤ N :=
    N.map_subtype_le (LinearMap.ker (ϕ.comp (Submodule.inclusion N_le_M)))
  refine ⟨M', M'_le_M, N', N'_le_N, N'_le_M', ?_⟩
  have y'_ortho_M' : ∀ (c : R), ∀ z ∈ M', c • y' + z = 0 → c = 0 := by
    intro c x xM' hc
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := Submodule.mem_map.mp xM'
    rw [LinearMap.mem_ker] at hx'
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := by exact @Subtype.coe_injective O (· ∈ M) _ _ hc
    simpa only [map_add, map_zero, map_smul, smul_eq_mul, add_zero, mul_eq_zero, ϕy'_ne_zero, hx',
      or_false] using congr_arg ϕ hc'
  have ay'_ortho_N' : ∀ (c : R), ∀ z ∈ N', c • a • y' + z = 0 → c = 0 := by
    intro c z zN' hc
    refine (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') ?_)).resolve_left a_zero
    rw [mul_comm, mul_smul, hc]
  refine ⟨y'_ortho_M', ay'_ortho_N', fun n' bN' ↦ ⟨?_, ?_⟩, ?_⟩
  · refine Module.Basis.mkFinConsOfLE y yN bN' N'_le_N ?_ ?_
    · intro c z zN' hc
      refine ay'_ortho_N' c z zN' ?_
      rwa [← a_smul_y'] at hc
    · intro z zN
      obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ :=
        Submodule.IsPrincipal.generator_submoduleImage_dvd_of_mem N_le_M ϕ zN
      refine ⟨-b, Submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, ?_, ?_⟩⟩
      · refine LinearMap.mem_ker.mpr (show ϕ (⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩) = 0 from ?_)
        rw [map_sub, map_smul, hb, ϕy_eq, smul_eq_mul, mul_comm, sub_self]
      · simp only [sub_eq_add_neg, neg_smul, Submodule.coe_subtype]
  · intro m' hn'm' bM'
    have hsp : ∀ (z : O), z ∈ M → ∃ (c : R), z + c • y' ∈ M' := by
      intro z zM
      refine ⟨-ϕ ⟨z, zM⟩, ⟨⟨z, zM⟩ - ϕ ⟨z, zM⟩ • ⟨y', y'M⟩, LinearMap.mem_ker.mpr ?_, ?_⟩⟩
      · rw [map_sub, map_smul, ϕy'_eq, smul_eq_mul, mul_one, sub_self]
      · rw [map_sub, map_smul, sub_eq_add_neg, neg_smul]
        rfl
    refine ⟨Nat.succ_le_succ hn'm',
      Module.Basis.mkFinConsOfLE y' y'M bM' M'_le_M y'_ortho_M' hsp, ?_, ?_⟩
    · intro as h
      refine ⟨Fin.cons a as, ?_, Fin.cons_zero _ _, fun i => Fin.cons_succ _ _ i⟩
      intro i
      rw [Module.Basis.coe_mkFinConsOfLE, Module.Basis.coe_mkFinConsOfLE]
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp only [Fin.cons_zero, Fin.castLE_zero]
        exact a_smul_y'.symm
      · rw [Fin.castLE_succ]
        simp only [Fin.cons_succ, Function.comp_apply, Submodule.coe_inclusion, h i]
    · intro j
      rw [Module.Basis.coe_mkFinConsOfLE]
      simp only [Fin.cons_succ, Function.comp_apply, Submodule.coe_inclusion]
  · exact fun x Ψ => aux_generator_dvd_all N_le_M ϕ_max y yN ϕy_eq x Ψ

/-- Strengthened copy of `Submodule.exists_smith_normal_form_of_le`: the diagonal
entries are nonzero and form a divisibility chain. -/
private theorem aux_exists_smith_of_le {ι : Type*} {R W : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Finite ι] [AddCommGroup W] [Module R W]
    (b : Module.Basis ι R W) (N O : Submodule R W) (N_le_O : N ≤ O) :
    ∃ (n o : ℕ) (hno : n ≤ o) (bO : Module.Basis (Fin o) R O)
      (bN : Module.Basis (Fin n) R N) (a : Fin n → R),
      (∀ i, (bN i : W) = a i • (bO (Fin.castLE hno i) : W)) ∧
      (∀ i, a i ≠ 0) ∧
      (∀ (i : ℕ) (hi1 : i < n) (hi2 : i + 1 < n), a ⟨i, hi1⟩ ∣ a ⟨i + 1, hi2⟩) := by
  cases nonempty_fintype ι
  induction O using Submodule.inductionOnRank b generalizing N with
  | ih M0 ih =>
    obtain ⟨m, b'M⟩ := M0.basisOfPid b
    by_cases N_bot : N = ⊥
    · subst N_bot
      exact ⟨0, m, Nat.zero_le _, b'M, Module.Basis.empty _, finZeroElim, finZeroElim,
        finZeroElim, fun i hi1 _ => absurd hi1 (Nat.not_lt_zero i)⟩
    · obtain ⟨y, hy, a, ha0, _hay, M', M'_le_M, N', N'_le_N, N'_le_M', y_ortho, _ay_ortho,
        hcons, hdiv⟩ :=
        aux_basis_of_pid M0 N b'M N_bot N_le_O
      obtain ⟨n', m', hn'm', bM', bN', as', has', hne', hchain'⟩ :=
        ih M' M'_le_M y hy y_ortho N' N'_le_M'
      obtain ⟨bN, h'⟩ := hcons n' bN'
      obtain ⟨hmn, bM, hcompat, hBshape⟩ := h' m' hn'm' bM'
      obtain ⟨as, has, h0, hsucc⟩ := hcompat as' has'
      refine ⟨n' + 1, m' + 1, hmn, bM, bN, as, has, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [h0]
          exact ha0
        · rw [hsucc i]
          exact hne' i
      · intro i hi1 hi2
        cases i with
        | zero =>
          have h0n' : 0 < n' := by omega
          have e0 : (⟨0, hi1⟩ : Fin (n' + 1)) = 0 := Fin.mk_zero
          have e1 : (⟨0, h0n'⟩ : Fin n').succ = (⟨0 + 1, hi2⟩ : Fin (n' + 1)) := rfl
          have hvN : (bN' ⟨0, h0n'⟩ : W) ∈ N := N'_le_N (bN' ⟨0, h0n'⟩).2
          have hdiv0 : a ∣ (bM.coord ((Fin.castLE hn'm' ⟨0, h0n'⟩).succ))
              ⟨(bN' ⟨0, h0n'⟩ : W), N_le_O hvN⟩ :=
            hdiv ⟨(bN' ⟨0, h0n'⟩ : W), hvN⟩ _
          have hcoord : (bM.coord ((Fin.castLE hn'm' ⟨0, h0n'⟩).succ))
              ⟨(bN' ⟨0, h0n'⟩ : W), N_le_O hvN⟩ = as' ⟨0, h0n'⟩ := by
            have hvec : (⟨(bN' ⟨0, h0n'⟩ : W), N_le_O hvN⟩ : ↥M0)
                = as' ⟨0, h0n'⟩ • bM ((Fin.castLE hn'm' ⟨0, h0n'⟩).succ) := by
              apply Subtype.ext
              change (bN' ⟨0, h0n'⟩ : W)
                = as' ⟨0, h0n'⟩ • ((bM ((Fin.castLE hn'm' ⟨0, h0n'⟩).succ) : ↥M0) : W)
              rw [hBshape]
              exact has' ⟨0, h0n'⟩
            rw [hvec, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self]
            simp
          rw [e0, ← e1, hsucc, h0]
          exact hcoord ▸ hdiv0
        | succ k =>
          have hk1 : k < n' := by omega
          have hk2 : k + 1 < n' := by omega
          have e1 : (⟨k + 1, hi1⟩ : Fin (n' + 1)) = (⟨k, hk1⟩ : Fin n').succ := rfl
          have e2 : (⟨k + 1 + 1, hi2⟩ : Fin (n' + 1)) = (⟨k + 1, hk2⟩ : Fin n').succ := rfl
          rw [e1, e2, hsucc, hsucc]
          exact hchain' k hk1 hk2

end MathlibExt.LinearAlgebra.SmithNormalFormWanted

/-!
# Smith normal form over a PID with a divisibility chain

Any submodule of a finite free module over a PID has diagonal bases whose coefficients are
nonzero and satisfy `a i ∣ a (i+1)`, refining `Submodule.exists_smith_normal_form_of_le`.
-/

namespace Submodule

/-- **Smith normal form with a divisibility chain.** Let $R$ be a principal ideal domain, let $M$
be a finitely generated free $R$-module and let $N$ be a submodule of $M$. Then there are natural
numbers $n \le m$, a basis $e_0, \dots, e_{m-1}$ of $M$, a basis $f_0, \dots, f_{n-1}$ of $N$ and
nonzero elements $a_0, \dots, a_{n-1}$ of $R$ such that $f_i = a_i e_i$ in $M$ for every $i < n$
and $a_i \mid a_{i+1}$ whenever $i + 1 < n$. -/
theorem exists_smith_normal_form_dvd_chain
    {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (N : Submodule R M) :
    ∃ (n m : ℕ) (hnm : n ≤ m) (bM : Module.Basis (Fin m) R M)
      (bN : Module.Basis (Fin n) R N) (a : Fin n → R),
      (∀ i, (bN i : M) = a i • bM (Fin.castLE hnm i)) ∧
      (∀ i, a i ≠ 0) ∧
      (∀ (i : ℕ) (hi1 : i < n) (hi2 : i + 1 < n), a ⟨i, hi1⟩ ∣ a ⟨i + 1, hi2⟩) := by
  obtain ⟨n, m, hnm, bO, bN, a, hcompat, hne, hchain⟩ :=
    MathlibExt.LinearAlgebra.SmithNormalFormWanted.aux_exists_smith_of_le
      (Module.finBasis R M) N ⊤ le_top
  refine ⟨n, m, hnm, bO.map (LinearEquiv.ofTop (⊤ : Submodule R M) rfl), bN, a, ?_, hne,
    hchain⟩
  intro i
  rw [Module.Basis.map_apply, LinearEquiv.ofTop_apply]
  exact hcompat i

end Submodule

namespace MathlibExt.LinearAlgebra.SmithNormalFormWanted

/--
**Smith normal form.** Let $R$ be a principal ideal domain, let $M$ be a finitely generated free
$R$-module and let $N$ be a submodule of $M$. Then there are natural numbers $n \le m$, a basis
$e_0, \dots, e_{m-1}$ of $M$, a basis $f_0, \dots, f_{n-1}$ of $N$ and nonzero elements
$a_0, \dots, a_{n-1}$ of $R$ such that $f_i = a_i e_i$ in $M$ for every $i < n$ and
$a_i \mid a_{i+1}$ whenever $i + 1 < n$.

Source: H. J. S. Smith, Phil. Trans. R. Soc. Lond. 151 (1861), 293-326, DOI 10.1098/RSTL.1861.0016.
It is `Submodule.exists_smith_normal_form_dvd_chain`, kept under the source's name.
Proves `Wanted` entry `smithNormalForm`.
-/
theorem smithNormalForm
    {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (N : Submodule R M) :
    ∃ (n m : ℕ) (hnm : n ≤ m) (bM : Module.Basis (Fin m) R M)
      (bN : Module.Basis (Fin n) R N) (a : Fin n → R),
      (∀ i, (bN i : M) = a i • bM (Fin.castLE hnm i)) ∧
      (∀ i, a i ≠ 0) ∧
      (∀ (i : ℕ) (hi1 : i < n) (hi2 : i + 1 < n), a ⟨i, hi1⟩ ∣ a ⟨i + 1, hi2⟩) := by
  exact Submodule.exists_smith_normal_form_dvd_chain N

end MathlibExt.LinearAlgebra.SmithNormalFormWanted
