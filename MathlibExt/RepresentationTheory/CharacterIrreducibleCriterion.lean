/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Maschke
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Character criterion for irreducibility

A finite-dimensional representation `σ` of a finite group `G` over an
algebraically closed field of characteristic zero is irreducible if and only
if the self-pairing of its character is `1`:
`⟨χ_σ, χ_σ⟩ = |G|⁻¹ ∑ g, χ_σ g * χ_σ g⁻¹ = 1`.

The forward direction is Mathlib's character orthogonality
(`Representation.char_orthonormal`). The converse is new: if the
intertwining algebra `σ.IntertwiningMap σ` is one-dimensional, then `σ` is
irreducible, and the self-pairing computes exactly that dimension
(`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`).

Source: `v1/Atlas/AlgebraNotes/code/Characters.lean` (target
`CharacterTheory.character_selfInnerProduct_corollary` /
`CharacterTheory.character_selfInnerProduct_irreducible_iff_aux` in
`v1/Atlas/AlgebraNotes/targets.yaml` / `report.json`). The v1 corollary also
contained the sum-of-squares formula for a character decomposed into
irreducibles; that part is not ported here.

This complements `CharacterTheory.irred_dim_dvd_card` (the dimension of an
irreducible representation divides `|G|`), which is the other
character-theoretic theorem from the same v1 file.
-/

@[expose] public section

namespace CharacterTheory

universe u

/-- **Class inner product.** Let $G$ be a finite group and $k$ a field in which $|G|$ is
invertible. For functions $f_1, f_2 \colon G \to k$, their class inner product is
$\langle f_1, f_2 \rangle = |G|^{-1} \sum_{g \in G} f_1(g) f_2(g^{-1})$. -/
noncomputable def classInnerProduct {G : Type u} [Group G] [Fintype G] {k : Type u}
    [Field k] [Invertible (Nat.card G : k)] (f₁ f₂ : G → k) : k :=
  (Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * f₂ g⁻¹

/-- A representation whose intertwining algebra is one-dimensional is
irreducible: every subrepresentation is the kernel or the whole space of a
projection, and a projection in a one-dimensional endomorphism algebra is a
scalar, hence `0` or `1`. -/
private theorem isIrreducible_of_finrank_intertwiningMap_eq_one
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Invertible (Nat.card G : k)] [IsAlgClosed k]
    (σ : Representation k G V)
    (hfr : Module.finrank k (σ.IntertwiningMap σ) = 1) :
    σ.IsIrreducible := by
  classical
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hfr_end : Module.finrank k (Module.End (MonoidAlgebra k G) σ.asModule) = 1 := by
    rw [← LinearEquiv.finrank_eq (Representation.IntertwiningMap.equivAlgEnd σ).toLinearEquiv]
    exact hfr
  have hV_ne : Nontrivial σ.asModule := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Module.finrank k (Module.End (MonoidAlgebra k G) σ.asModule) = 0 :=
      @Module.finrank_zero_of_subsingleton _ _ _ _ _ _
        ⟨fun f g => LinearMap.ext fun x => @Subsingleton.elim _ hnt _ _⟩
    linarith
  have hid_ne : (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule) ≠ 0 := by
    intro heq
    obtain ⟨x, y, hxy⟩ := hV_ne.exists_pair_ne
    have hx := LinearMap.ext_iff.mp heq x
    have hy := LinearMap.ext_iff.mp heq y
    simp only [LinearMap.id_apply, LinearMap.zero_apply] at hx hy
    exact hxy (by rw [hx, hy])
  exact {
    exists_pair_ne := ⟨⊥, ⊤, by
      intro heq
      obtain ⟨x, y, hxy⟩ := hV_ne.exists_pair_ne
      have hx : x ∈ (⊥ : Submodule (MonoidAlgebra k G) σ.asModule) :=
        heq ▸ Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule (MonoidAlgebra k G) σ.asModule) :=
        heq ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      exact hxy (by rw [hx, hy])⟩
    eq_bot_or_eq_top := fun S => by
      obtain ⟨T, hST⟩ := MonoidAlgebra.Submodule.exists_isCompl S
      set p := S.subtype.comp (S.projectionOnto T hST)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid_ne).mp hfr_end p
      have hp_idem : p.comp p = p := by
        ext x
        simp only [p, LinearMap.comp_apply, Submodule.subtype_apply]
        congr 1
        exact Submodule.projectionOnto_apply_left hST _
      have hc2 : c * c = c := by
        have h1 : (c * c) • (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule) =
            c • LinearMap.id := by
          have hcomp : (c • (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule)).comp
              (c • LinearMap.id) = (c * c) • LinearMap.id := by
            ext x
            simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
          have hcomp2 : (c • (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule)).comp
              (c • LinearMap.id) = c • LinearMap.id := by
            have := hp_idem
            rw [← hc] at this
            exact this
          rw [← hcomp]
          exact hcomp2
        have h2 : (c * c - c) • (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule) = 0 := by
          have hsub := sub_smul (c * c) c
            (LinearMap.id : Module.End (MonoidAlgebra k G) σ.asModule)
          rw [h1] at hsub
          rw [hsub, sub_self]
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exact sub_eq_zero.mp h3
        · exact absurd h3 hid_ne
      have hc01 : c = 0 ∨ c = 1 := by
        have h3 : c * (c - 1) = 0 := by linear_combination hc2
        rcases mul_eq_zero.mp h3 with h4 | h4
        · left
          exact h4
        · right
          exact sub_eq_zero.mp h4
      rcases hc01 with rfl | rfl
      · left
        have hp0 : p = 0 := by rw [hc.symm]; simp only [zero_smul]
        ext x
        constructor
        · intro hx
          have hmem : (S.projectionOnto T hST x : σ.asModule) = x :=
            congrArg Subtype.val (Submodule.projectionOnto_apply_of_mem_left hST hx)
          have h0 : (p x : σ.asModule) = 0 := by
            have := LinearMap.ext_iff.mp hp0 x
            simp only [LinearMap.zero_apply] at this
            exact this
          simp only [p, LinearMap.comp_apply, Submodule.subtype_apply] at h0
          rw [← hmem]
          exact h0
        · intro hx
          simp only [Submodule.mem_bot] at hx
          rw [hx]
          exact S.zero_mem
      · right
        rw [eq_top_iff]
        intro x _
        have hp1 : p = LinearMap.id := by rw [hc.symm]; simp only [one_smul]
        have hpx : (↑(S.projectionOnto T hST x) : σ.asModule) = x := by
          have h := LinearMap.ext_iff.mp hp1 x
          simp only [p, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at h
          exact h
        exact hpx ▸ (S.projectionOnto T hST x).2
  }

/-- **Character criterion for irreducibility.** A finite-dimensional
representation `σ` of a finite group over an algebraically closed field of
characteristic zero is irreducible if and only if the self-pairing of its
character is `1`. -/
public theorem irreducible_iff_classInnerProduct_self_eq_one
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Invertible (Nat.card G : k)] [IsAlgClosed k] [CharZero k]
    (σ : Representation k G V) :
    σ.IsIrreducible ↔ classInnerProduct σ.character σ.character = 1 := by
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ σ
  simp only [classInnerProduct]
  constructor
  · intro hirr
    rw [key, Representation.IsIrreducible.finrank_intertwiningMap_self σ]
    norm_cast
  · intro h
    rw [key] at h
    have hfr : Module.finrank k (σ.IntertwiningMap σ) = 1 := by exact_mod_cast h
    exact isIrreducible_of_finrank_intertwiningMap_eq_one σ hfr

end CharacterTheory
