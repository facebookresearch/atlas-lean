/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
public import MathlibExt.AlgebraicTopology.SimplexCategory.GeneratorsRelations.DeltaChain

/-!
# Generators-and-relations equivalence

This module completes the generators-and-relations presentation of `SimplexCategory`:
canonical-object fullness and faithfulness assemble into the equivalence
`SimplexCategoryGenRel ≌ SimplexCategory`, with the canonical-object inverse
`fromSimplexCategory`. It is the bridge from presented `Data` to genuine
simplicial objects. It reuses the `DeltaChain` / `P_σ` normal forms rather than
defining a second simplex category.
-/

@[expose] public section

namespace SimplexCategoryGenRel

open CategoryTheory CategoryTheory.Limits


section StandardSigmaProofIrrelevance

theorem standardσ_eq_of_eq {L : List ℕ} {m₁ m₂ : ℕ}
    (h₁ h₂ : m₂ + L.length = m₁) : standardσ L h₁ = standardσ L h₂ := by
  cases Subsingleton.elim h₁ h₂
  rfl

end StandardSigmaProofIrrelevance

section P_sigma_fixed

/--
Fixed-endpoint corollary of `exists_normal_form_P_σ`: any `P_σ`
morphism between canonical objects is an admissible `standardσ` with no
object transports in the statement.
-/
theorem exists_admissible_standardσ_of_P_σ {n m : ℕ}
    (f : mk n ⟶ mk m) (hf : P_σ f) :
    ∃ L : List ℕ, ∃ (h : m + L.length = n),
      IsAdmissible m L ∧ f = standardσ L h := by
  obtain ⟨L, m₀, b, h₁, h₂, h_len, hA, hf_eq⟩ := exists_normal_form_P_σ f hf
  have hm₀ : m₀ = m := by
    simpa using congrArg len h₁
  have h_eq : m + L.length = n := by
    have h_eq' : len (mk m) + L.length = len (mk n) := by
      rw [h_len, h₁.symm, h₂]
      rfl
    simpa using h_eq'
  have hA' : IsAdmissible m L := hm₀ ▸ hA
  refine ⟨L, h_eq, ⟨hA', ?_⟩⟩
  calc f = _ := hf_eq
    _ = standardσ L h_eq := by
      apply standardσ_eq_of_eq

end P_sigma_fixed

section P_sigma_uniqueness

private lemma mem_lt_of_mem_isAdmissible {m : ℕ} {L : List ℕ}
    (hL : IsAdmissible m L) {a : ℕ} (ha : a ∈ L) : a < m + L.length := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
  exact IsAdmissible.getElem_lt hL (k := k) (hk := hk)

private lemma not_mem_of_le_isAdmissible {m : ℕ} {L : List ℕ}
    (hL : IsAdmissible m L) {a : ℕ} (ha : m + L.length ≤ a) : a ∉ L := by
  intro hm
  have hlt := mem_lt_of_mem_isAdmissible hL hm
  omega

/--
Uniqueness of admissible `standardσ` lists from equality after
`toSimplexCategory.map`. Uses `mem_isAdmissible_iff` and
`simplicialEvalσ_of_isAdmissible` and handles values outside the common source
bound explicitly.
-/
theorem IsAdmissible.eq_of_toSimplexCategory_map_eq_standardσ {n m : ℕ}
    {L₁ L₂ : List ℕ} {h₁ : m + L₁.length = n} {h₂ : m + L₂.length = n}
    (hA₁ : IsAdmissible m L₁) (hA₂ : IsAdmissible m L₂)
    (h : toSimplexCategory.map (standardσ L₁ h₁) = toSimplexCategory.map (standardσ L₂ h₂)) :
    L₁ = L₂ := by
  have h_ord :
      (toSimplexCategory.map (standardσ L₁ h₁)).toOrderHom =
      (toSimplexCategory.map (standardσ L₂ h₂)).toOrderHom := by
    rw [h]
  have h_eval : ∀ j (hj : j < n + 1), simplicialEvalσ L₁ j = simplicialEvalσ L₂ j := by
    intro j hj
    have e₁ := simplicialEvalσ_of_isAdmissible (m₁ := n) (m₂ := m) (L := L₁) hA₁ h₁ j hj
    have e₂ := simplicialEvalσ_of_isAdmissible (m₁ := n) (m₂ := m) (L := L₂) hA₂ h₂ j hj
    -- e₁ : ↑(toOrderHom₁ ⟨j, _⟩) = simplicialEvalσ L₁ j
    calc simplicialEvalσ L₁ j
        = ↑((toSimplexCategory.map (standardσ L₁ h₁)).toOrderHom ⟨j, hj⟩) := e₁.symm
      _ = ↑((toSimplexCategory.map (standardσ L₂ h₂)).toOrderHom ⟨j, hj⟩) := by
          rw [h_ord]
      _ = simplicialEvalσ L₂ j := e₂
  have h_mem : ∀ a, a ∈ L₁ ↔ a ∈ L₂ := by
    intro a
    by_cases ha_lt : a < n
    · have iff1 : a ∈ L₁ ↔
          a < n ∧ simplicialEvalσ L₁ a = simplicialEvalσ L₁ (a + 1) := by
        have hm1 := mem_isAdmissible_iff (m := m) (L := L₁) hA₁ a
        calc a ∈ L₁ ↔ a < m + L₁.length ∧ simplicialEvalσ L₁ a = simplicialEvalσ L₁ (a + 1) := hm1
          _ ↔ a < n ∧ simplicialEvalσ L₁ a = simplicialEvalσ L₁ (a + 1) := by rw [h₁]
      have iff2 : a ∈ L₂ ↔
          a < n ∧ simplicialEvalσ L₂ a = simplicialEvalσ L₂ (a + 1) := by
        have hm2 := mem_isAdmissible_iff (m := m) (L := L₂) hA₂ a
        calc a ∈ L₂ ↔ a < m + L₂.length ∧ simplicialEvalσ L₂ a = simplicialEvalσ L₂ (a + 1) := hm2
          _ ↔ a < n ∧ simplicialEvalσ L₂ a = simplicialEvalσ L₂ (a + 1) := by rw [h₂]
      rw [iff1, iff2]
      have ha1_lt : a + 1 < n + 1 := by omega
      have h_eq_a : simplicialEvalσ L₁ a = simplicialEvalσ L₂ a :=
        h_eval a (by omega)
      have h_eq_succ : simplicialEvalσ L₁ (a + 1) = simplicialEvalσ L₂ (a + 1) :=
        h_eval (a + 1) ha1_lt
      constructor
      · rintro ⟨_, heq⟩
        exact ⟨ha_lt, by rw [← h_eq_a, ← h_eq_succ]; exact heq⟩
      · rintro ⟨_, heq⟩
        exact ⟨ha_lt, by rw [h_eq_a, h_eq_succ]; exact heq⟩
    · have ha_ge : n ≤ a := Nat.not_lt.mp ha_lt
      have h_ge1 : m + L₁.length ≤ a := by rw [h₁]; exact ha_ge
      have h_ge2 : m + L₂.length ≤ a := by rw [h₂]; exact ha_ge
      have not1 : a ∉ L₁ := not_mem_of_le_isAdmissible hA₁ h_ge1
      have not2 : a ∉ L₂ := not_mem_of_le_isAdmissible hA₂ h_ge2
      simp [not1, not2]
  have h_pair1 : L₁.Pairwise (· < ·) :=
    (isAdmissible_iff_pairwise_and_le.mp hA₁).1
  have h_pair2 : L₂.Pairwise (· < ·) :=
    (isAdmissible_iff_pairwise_and_le.mp hA₂).1
  exact List.Pairwise.eq_of_mem_iff h_pair1 h_pair2 h_mem

end P_sigma_uniqueness

section P_sigma_faithfulness

/-- Public `P_σ` faithfulness for fixed canonical endpoints. -/
theorem eq_of_toSimplexCategory_map_eq_of_P_sigma {n m : ℕ} {f g : mk n ⟶ mk m}
    (hf : P_σ f) (hg : P_σ g)
    (h : toSimplexCategory.map f = toSimplexCategory.map g) : f = g := by
  obtain ⟨L₁, h₁, hA₁, hf_eq⟩ := exists_admissible_standardσ_of_P_σ f hf
  obtain ⟨L₂, h₂, hA₂, hg_eq⟩ := exists_admissible_standardσ_of_P_σ g hg
  have h_map : toSimplexCategory.map (standardσ L₁ h₁) =
               toSimplexCategory.map (standardσ L₂ h₂) := by
    rw [← hf_eq, ← hg_eq]
    exact h
  have hL_eq : L₁ = L₂ :=
    IsAdmissible.eq_of_toSimplexCategory_map_eq_standardσ hA₁ hA₂ h_map
  subst hL_eq
  have h_eq : h₁ = h₂ := Subsingleton.elim _ _
  subst h_eq
  rw [hf_eq, hg_eq]

end P_sigma_faithfulness

section EpiLifting

/--
Epi-lifting to pure degeneracies for canonical simplex objects.

Uses `SimplexCategory.le_of_epi` for the length bound, `SimplexCategory.eq_id_of_epi`
in the equal-length case, and `SimplexCategory.eq_σ_comp_of_not_injective` after
showing non-injectivity via mono+epi ⇒ iso in the strict case. The residual map
is epi by cancellation and the induction goes through on the strictly smaller source,
prepending the corresponding `σ` in `GenRel` with `P_σ.comp_mem`.
-/
theorem exists_preimage_of_epi {n m : ℕ} (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    [Epi θ] :
    ∃ f : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk m,
      P_σ f ∧ toSimplexCategory.map f = θ := by
  -- Induction on the source length keeps all endpoints canonical.
  suffices h : ∀ (n : ℕ) (m : ℕ) (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) [Epi θ],
      ∃ f : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk m,
        P_σ f ∧ toSimplexCategory.map f = θ from h n m θ
  intro n
  induction n with
  | zero =>
    intro m θ hEpiInst
    have : Epi θ := hEpiInst
    have hm_le : m ≤ 0 := SimplexCategory.le_of_epi θ
    have hm_eq : m = 0 := Nat.le_zero.mp hm_le
    subst hm_eq
    -- θ : ⦋0⦌ ⟶ ⦋0⦌ is epi hence the identity.
    have hθ_id : θ = 𝟙 (SimplexCategory.mk 0) := SimplexCategory.eq_id_of_epi θ
    exact ⟨𝟙 (SimplexCategoryGenRel.mk 0), P_σ.id_mem _, by simp [hθ_id]⟩
  | succ k ih =>
    intro m θ hEpiInst
    have hEpi : Epi θ := hEpiInst
    have hm_le : m ≤ k + 1 := SimplexCategory.le_of_epi θ
    by_cases hm_eq : m = k + 1
    · subst hm_eq
      -- Equal-length epi is the identity on the canonical object.
      have hθ_id : θ = 𝟙 (SimplexCategory.mk (k + 1)) := SimplexCategory.eq_id_of_epi θ
      exact ⟨𝟙 (SimplexCategoryGenRel.mk (k + 1)), P_σ.id_mem _, by simp [hθ_id]⟩
    · -- Strict case m < k+1, hence m ≤ k.
      have hm_lt : m < k + 1 := Nat.lt_of_le_of_ne hm_le hm_eq
      -- θ cannot be injective, otherwise it would be mono and epi, hence its
      -- lengths would coincide, contradicting strict inequality.  Avoids IsIso
      -- synthesis by using len_le_of_mono directly.
      have h_not_injective : ¬Function.Injective θ.toOrderHom := by
        intro h_inj
        have hMono : Mono θ := (SimplexCategory.mono_iff_injective.mpr h_inj)
        have h_le_mono : k + 1 ≤ m := by
          have h := SimplexCategory.len_le_of_mono θ
          simpa [SimplexCategory.len_mk] using h
        exact hm_eq (Nat.le_antisymm hm_le h_le_mono)
      obtain ⟨i, θ', hθ_eq⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ h_not_injective
      -- The residual θ' is epi by cancellation: epi (σ i ≫ θ') implies epi θ'.
      have h_epi_comp : Epi (SimplexCategory.σ i ≫ θ') := by
        rw [← hθ_eq]
        exact hEpi
      have h_epi_res : Epi θ' := CategoryTheory.epi_of_epi (SimplexCategory.σ i) θ'
      -- Recurse on the strictly smaller source k.
      obtain ⟨f', hf'_P, hf'_eq⟩ := ih m θ'
      refine ⟨SimplexCategoryGenRel.σ i ≫ f', ?_, ?_⟩
      · exact P_σ.comp_mem _ _ (P_σ.σ i) hf'_P
      · have h_map : toSimplexCategory.map (SimplexCategoryGenRel.σ i ≫ f') = θ := by
          simp [hf'_eq, hθ_eq.symm]
        exact h_map

end EpiLifting

section MonoLifting

/--
Mono-lifting to admissible face chains for canonical simplex objects.

Uses `SimplexCategory.le_of_mono` for the length bound, `SimplexCategory.eq_id_of_mono`
in the equal-length case, and `SimplexCategory.eq_comp_δ_of_not_surjective` after showing
non-surjectivity via epi+mono ⇒ iso in the strict case. The residual map is mono by
cancellation and the induction goes through on the strictly smaller target, forming
`DeltaChain.normalize (c.snoc i)` with `normalize_admissible`, `normalize_eval`,
functoriality, and the recursive map equality.
-/
theorem exists_preimage_of_mono {n m : ℕ} (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    [Mono θ] :
    ∃ c : DeltaChain n m, DeltaChain.Admissible c ∧
      toSimplexCategory.map c.eval = θ := by
  suffices h : ∀ (m : ℕ) (n : ℕ) (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) [Mono θ],
      ∃ c : DeltaChain n m, DeltaChain.Admissible c ∧ toSimplexCategory.map c.eval = θ from
    h m n θ
  intro m
  induction m with
  | zero =>
    intro n θ hMonoInst
    have : Mono θ := hMonoInst
    have h_le : n ≤ 0 := SimplexCategory.le_of_mono θ
    have h_eq : n = 0 := Nat.le_zero.mp h_le
    subst h_eq
    have h_id : θ = 𝟙 (SimplexCategory.mk 0) := SimplexCategory.eq_id_of_mono θ
    refine ⟨DeltaChain.nil, DeltaChain.Admissible.nil, ?_⟩
    simp [DeltaChain.eval_nil, h_id]
  | succ m ih =>
    intro n θ hMonoInst
    have hMono : Mono θ := hMonoInst
    have h_le : n ≤ m + 1 := SimplexCategory.le_of_mono θ
    by_cases h_eq : n = m + 1
    · subst h_eq
      have h_id : θ = 𝟙 (SimplexCategory.mk (m + 1)) := SimplexCategory.eq_id_of_mono θ
      refine ⟨DeltaChain.nil (n := m + 1), DeltaChain.Admissible.nil, ?_⟩
      simp [DeltaChain.eval_nil, h_id]
    · have h_lt : n < m + 1 := Nat.lt_of_le_of_ne h_le h_eq
      have h_not_surj : ¬Function.Surjective θ.toOrderHom := by
        intro h_surj
        have : Epi θ := (SimplexCategory.epi_iff_surjective.mpr h_surj)
        have h_le_epi : m + 1 ≤ n := SimplexCategory.le_of_epi θ
        omega
      obtain ⟨i, θ', hθ_eq⟩ := SimplexCategory.eq_comp_δ_of_not_surjective θ h_not_surj
      have : Mono (θ' ≫ SimplexCategory.δ i) := by
        rw [← hθ_eq]
        infer_instance
      have : Mono θ' := CategoryTheory.mono_of_mono θ' (SimplexCategory.δ i)
      obtain ⟨c', hc'_adm, hc'_eq⟩ := ih n θ'
      have h_map_snoc : toSimplexCategory.map (c'.snoc i).eval = θ := by
        simp [hc'_eq, hθ_eq.symm]
      refine ⟨DeltaChain.normalize (c'.snoc i), DeltaChain.normalize_admissible _, ?_⟩
      have h_norm : toSimplexCategory.map (DeltaChain.normalize (c'.snoc i)).eval = θ := by
        rw [DeltaChain.normalize_eval]
        exact h_map_snoc
      exact h_norm

end MonoLifting

section Fullness

/--
Canonical-object fullness from the strong epi--mono factorization.

Uses `factorThruImage`, `image.ι`, and `image.fac` in `SimplexCategory`,
transports the image object to `mk (image θ).len` only at the outer boundary
via `SimplexCategory.ext` and `eqToHom`, then reuses `exists_preimage_of_epi`
and `exists_preimage_of_mono`.
-/
theorem exists_preimage {n m : ℕ}
    (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    ∃ f : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk m,
      toSimplexCategory.map f = θ := by
  let Img := image θ
  let k := Img.len
  have h_mk_eq_Img : SimplexCategory.mk k = Img := by
    apply SimplexCategory.ext
    rfl
  have h_Img_eq_mk : Img = SimplexCategory.mk k := h_mk_eq_Img.symm
  let e₀ : SimplexCategory.mk n ⟶ Img := factorThruImage θ
  let i₀ : Img ⟶ SimplexCategory.mk m := image.ι θ
  have h_fac : e₀ ≫ i₀ = θ := image.fac θ
  let e' : SimplexCategory.mk n ⟶ SimplexCategory.mk k :=
    e₀ ≫ eqToHom h_Img_eq_mk
  let i' : SimplexCategory.mk k ⟶ SimplexCategory.mk m :=
    eqToHom h_mk_eq_Img ≫ i₀
  have h_mid : eqToHom h_Img_eq_mk ≫ eqToHom h_mk_eq_Img = 𝟙 Img := by
    rw [eqToHom_trans]
    have : h_Img_eq_mk.trans h_mk_eq_Img = rfl := by
      apply Subsingleton.elim
    rw [this, eqToHom_refl]
  have h_e'i' : e' ≫ i' = θ := by
    have h1 : e' ≫ i' = e₀ ≫ eqToHom h_Img_eq_mk ≫ eqToHom h_mk_eq_Img ≫ i₀ := by
      simp [e', i']
    have h2 : e₀ ≫ eqToHom h_Img_eq_mk ≫ eqToHom h_mk_eq_Img ≫ i₀ =
        e₀ ≫ (eqToHom h_Img_eq_mk ≫ eqToHom h_mk_eq_Img) ≫ i₀ := by
      simp only [Category.assoc]
    have h3 : e₀ ≫ (eqToHom h_Img_eq_mk ≫ eqToHom h_mk_eq_Img) ≫ i₀ =
        e₀ ≫ 𝟙 Img ≫ i₀ := by rw [h_mid]
    have h4 : e₀ ≫ 𝟙 Img ≫ i₀ = e₀ ≫ i₀ := by simp
    rw [h1, h2, h3, h4, h_fac]
  have he₀ : Epi e₀ := inferInstance
  have hi₀ : Mono i₀ := inferInstance
  have he_iso : Epi (eqToHom h_Img_eq_mk) := inferInstance
  have hi_iso : Mono (eqToHom h_mk_eq_Img) := inferInstance
  have he' : Epi e' := epi_comp' he₀ he_iso
  have hi' : Mono i' := mono_comp' hi_iso hi₀
  obtain ⟨f_e, _hf_e_P, hf_e_eq⟩ := @exists_preimage_of_epi _ _ e' he'
  obtain ⟨c_i, _hc_i_adm, hc_i_eq⟩ := @exists_preimage_of_mono _ _ i' hi'
  refine ⟨f_e ≫ c_i.eval, ?_⟩
  have h_map_comp : toSimplexCategory.map (f_e ≫ c_i.eval) =
      toSimplexCategory.map f_e ≫ toSimplexCategory.map c_i.eval := by
    rw [Functor.map_comp]
  have h1 : toSimplexCategory.map f_e ≫ toSimplexCategory.map c_i.eval =
      e' ≫ toSimplexCategory.map c_i.eval :=
    congrArg (· ≫ toSimplexCategory.map c_i.eval) hf_e_eq
  have h2 : e' ≫ toSimplexCategory.map c_i.eval = e' ≫ i' :=
    congrArg (e' ≫ ·) hc_i_eq
  have h_eq : toSimplexCategory.map (f_e ≫ c_i.eval) = e' ≫ i' :=
    h_map_comp.trans (h1.trans h2)
  exact h_eq.trans h_e'i'

end Fullness

section CanonicalFactorization

/--
Every morphism between canonical presented simplex objects factors as a pure degeneracy
followed by an admissible face-chain. Uses `exists_P_σ_P_δ_factorization` for the
`P_σ / P_δ` split, reduces the intermediate object with dependent object induction
`SimplexCategoryGenRel.rec`, and finishes with `DeltaChain.exists_admissible_chain_of_P_delta`.
-/
theorem exists_canonical_P_sigma_deltaChain_factorization {n m : ℕ}
    (f : mk n ⟶ mk m) :
    ∃ k, ∃ (e : mk n ⟶ mk k), ∃ (c : DeltaChain k m),
      P_σ e ∧ DeltaChain.Admissible c ∧ f = e ≫ c.eval := by
  obtain ⟨z, e, d, he, hd, hfd⟩ := exists_P_σ_P_δ_factorization f
  have hcanon :
      ∀ (z : SimplexCategoryGenRel) (e : mk n ⟶ z) (d : z ⟶ mk m),
        P_σ e → P_δ d →
          ∃ k, ∃ (e' : mk n ⟶ mk k), ∃ (c : DeltaChain k m),
            P_σ e' ∧ DeltaChain.Admissible c ∧ e ≫ d = e' ≫ c.eval := by
    apply SimplexCategoryGenRel.rec
    intro k e d he hd
    obtain ⟨c, hc_adm, hc_eq⟩ := DeltaChain.exists_admissible_chain_of_P_delta d hd
    exact ⟨k, e, c, he, hc_adm, by rw [hc_eq]⟩
  obtain ⟨k, e', c, he', hc_adm, heq⟩ := hcanon z e d he hd
  exact ⟨k, e', c, he', hc_adm, hfd.trans heq⟩

end CanonicalFactorization

section Faithfulness

/--
Canonical-endpoint injectivity of `toSimplexCategory.map` via the
`P_σ`-`DeltaChain` factorisation and simplex image uniqueness.
Both factors become epi/mono after `toSimplexCategory.map` via
`isSplitEpi_toSimplexCategory_map_of_P_σ`,
`isSplitMono_toSimplexCategory_map_of_P_δ` and `DeltaChain.eval_mem_P_delta`.
Their common image is compared with `SimplexCategory.image_eq`,
`SimplexCategory.factorThruImage_eq` and `SimplexCategory.image_ι_eq`,
with all `image θ = mk k` transports handled proof-irrelevantly.
-/
theorem eq_of_toSimplexCategory_map_eq {n m : ℕ} {f g : mk n ⟶ mk m}
    (h : toSimplexCategory.map f = toSimplexCategory.map g) : f = g := by
  obtain ⟨k₁, e₁, c₁, he₁, hc₁, hf_eq⟩ :=
    exists_canonical_P_sigma_deltaChain_factorization f
  obtain ⟨k₂, e₂, c₂, he₂, hc₂, hg_eq⟩ :=
    exists_canonical_P_sigma_deltaChain_factorization g
  let θ := toSimplexCategory.map f
  have h_fac1 : toSimplexCategory.map e₁ ≫ toSimplexCategory.map c₁.eval = θ := by
    rw [← Functor.map_comp, ← hf_eq]
  have h_fac2 : toSimplexCategory.map e₂ ≫ toSimplexCategory.map c₂.eval = θ := by
    rw [← Functor.map_comp, ← hg_eq, h.symm]
  -- epi/mono after `map` via split epi/mono
  have h_split_epi1 : IsSplitEpi (toSimplexCategory.map e₁) :=
    isSplitEpi_toSimplexCategory_map_of_P_σ he₁
  have h_epi1 : Epi (toSimplexCategory.map e₁) :=
    h_split_epi1.exists_splitEpi.some.epi
  have h_split_epi2 : IsSplitEpi (toSimplexCategory.map e₂) :=
    isSplitEpi_toSimplexCategory_map_of_P_σ he₂
  have h_epi2 : Epi (toSimplexCategory.map e₂) :=
    h_split_epi2.exists_splitEpi.some.epi
  have h_split_mono1 : IsSplitMono (toSimplexCategory.map c₁.eval) :=
    isSplitMono_toSimplexCategory_map_of_P_δ (DeltaChain.eval_mem_P_delta c₁)
  have h_mono1 : Mono (toSimplexCategory.map c₁.eval) :=
    SplitMono.mono h_split_mono1.exists_splitMono.some
  have h_split_mono2 : IsSplitMono (toSimplexCategory.map c₂.eval) :=
    isSplitMono_toSimplexCategory_map_of_P_δ (DeltaChain.eval_mem_P_delta c₂)
  have h_mono2 : Mono (toSimplexCategory.map c₂.eval) :=
    SplitMono.mono h_split_mono2.exists_splitMono.some
  -- both factorizations exhibit the same simplex image
  have h_img1 : image θ = SimplexCategory.mk k₁ :=
    @SimplexCategory.image_eq _ _ _ _ _ h_epi1 _ h_mono1 h_fac1
  have h_img2 : image θ = SimplexCategory.mk k₂ :=
    @SimplexCategory.image_eq _ _ _ _ _ h_epi2 _ h_mono2 h_fac2
  have h_mk_eq : SimplexCategory.mk k₁ = SimplexCategory.mk k₂ :=
    h_img1.symm.trans h_img2
  have hk_eq : k₁ = k₂ := by
    have h_len := congrArg SimplexCategory.len h_mk_eq
    simpa using h_len
  subst hk_eq
  have h_img2' : image θ = SimplexCategory.mk k₁ := h_img2
  have h_img_eq : h_img1 = h_img2' := Subsingleton.elim _ _
  -- also transport to `toSimplexCategory.obj (mk k₁)` to match `map` codomains
  have h_obj_mk : toSimplexCategory.obj (mk k₁) = SimplexCategory.mk k₁ := rfl
  have h_img1_obj : image θ = toSimplexCategory.obj (mk k₁) := by
    rw [h_obj_mk.symm.symm]
    -- `image θ = mk k₁ = obj (mk k₁)` needs proof irrelevance at boundary
    calc image θ = SimplexCategory.mk k₁ := h_img1
      _ = toSimplexCategory.obj (mk k₁) := h_obj_mk.symm
  have h_img2'_obj : image θ = toSimplexCategory.obj (mk k₁) := by
    calc image θ = SimplexCategory.mk k₁ := h_img2'
      _ = toSimplexCategory.obj (mk k₁) := h_obj_mk.symm
  have h_cancel1 :
      eqToHom h_img1_obj.symm ≫ eqToHom h_img1_obj =
        𝟙 (toSimplexCategory.obj (mk k₁)) := by
    rw [eqToHom_trans]
    have : h_img1_obj.symm.trans h_img1_obj = rfl := Subsingleton.elim _ _
    rw [this, eqToHom_refl]
  have h_cancel2 :
      eqToHom h_img2'_obj.symm ≫ eqToHom h_img2'_obj =
        𝟙 (toSimplexCategory.obj (mk k₁)) := by
    rw [eqToHom_trans]
    have : h_img2'_obj.symm.trans h_img2'_obj = rfl := Subsingleton.elim _ _
    rw [this, eqToHom_refl]
  have h_fac1' :
      (toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm) ≫
        (eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval) = θ := by
    calc (toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm) ≫
          (eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval)
        = toSimplexCategory.map e₁ ≫
            (eqToHom h_img1_obj.symm ≫
              (eqToHom h_img1_obj ≫
                toSimplexCategory.map c₁.eval)) := by
          rw [Category.assoc]
      _ = toSimplexCategory.map e₁ ≫
            ((eqToHom h_img1_obj.symm ≫ eqToHom h_img1_obj) ≫
              toSimplexCategory.map c₁.eval) := by
          rw [← Category.assoc
            (eqToHom h_img1_obj.symm) (eqToHom h_img1_obj) _]
      _ = toSimplexCategory.map e₁ ≫
            (𝟙 _ ≫ toSimplexCategory.map c₁.eval) := by
          rw [h_cancel1]
      _ = toSimplexCategory.map e₁ ≫ toSimplexCategory.map c₁.eval := by
          rw [Category.id_comp]
      _ = θ := h_fac1
  have h_fac2' :
      (toSimplexCategory.map e₂ ≫ eqToHom h_img2'_obj.symm) ≫
        (eqToHom h_img2'_obj ≫ toSimplexCategory.map c₂.eval) = θ := by
    calc (toSimplexCategory.map e₂ ≫ eqToHom h_img2'_obj.symm) ≫
          (eqToHom h_img2'_obj ≫ toSimplexCategory.map c₂.eval)
        = toSimplexCategory.map e₂ ≫
            (eqToHom h_img2'_obj.symm ≫
              (eqToHom h_img2'_obj ≫
                toSimplexCategory.map c₂.eval)) := by
          rw [Category.assoc]
      _ = toSimplexCategory.map e₂ ≫
            ((eqToHom h_img2'_obj.symm ≫ eqToHom h_img2'_obj) ≫
              toSimplexCategory.map c₂.eval) := by
          rw [← Category.assoc
            (eqToHom h_img2'_obj.symm) (eqToHom h_img2'_obj) _]
      _ = toSimplexCategory.map e₂ ≫
            (𝟙 _ ≫ toSimplexCategory.map c₂.eval) := by
          rw [h_cancel2]
      _ = toSimplexCategory.map e₂ ≫ toSimplexCategory.map c₂.eval := by
          rw [Category.id_comp]
      _ = θ := h_fac2
  have h_epi_e₁' : Epi (toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm) :=
    epi_comp' h_epi1 inferInstance
  have h_epi_e₂' : Epi (toSimplexCategory.map e₂ ≫ eqToHom h_img2'_obj.symm) :=
    epi_comp' h_epi2 inferInstance
  have h_mono_i₁' : Mono (eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval) :=
    mono_comp' inferInstance h_mono1
  have h_mono_i₂' : Mono (eqToHom h_img2'_obj ≫ toSimplexCategory.map c₂.eval) :=
    mono_comp' inferInstance h_mono2
  have h_e'_eq :
      toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm = factorThruImage θ :=
    (@SimplexCategory.factorThruImage_eq _ _ _
      (toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm)
      h_epi_e₁'
      (eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval)
      h_mono_i₁' h_fac1').symm
  have h_e₂'_eq :
      toSimplexCategory.map e₂ ≫ eqToHom h_img2'_obj.symm = factorThruImage θ :=
    (@SimplexCategory.factorThruImage_eq _ _ _
      (toSimplexCategory.map e₂ ≫ eqToHom h_img2'_obj.symm)
      h_epi_e₂'
      (eqToHom h_img2'_obj ≫ toSimplexCategory.map c₂.eval)
      h_mono_i₂' h_fac2').symm
  have h_i'_eq :
      eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval = image.ι θ :=
    (@SimplexCategory.image_ι_eq _ _ _
      (toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm)
      h_epi_e₁'
      (eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval)
      h_mono_i₁' h_fac1').symm
  have h_i₂'_eq :
      eqToHom h_img2'_obj ≫ toSimplexCategory.map c₂.eval = image.ι θ :=
    (@SimplexCategory.image_ι_eq _ _ _
      (toSimplexCategory.map e₂ ≫ eqToHom h_img2'_obj.symm)
      h_epi_e₂'
      (eqToHom h_img2'_obj ≫ toSimplexCategory.map c₂.eval)
      h_mono_i₂' h_fac2').symm
  have h_e12' : toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm =
      toSimplexCategory.map e₂ ≫ eqToHom h_img2'_obj.symm :=
    h_e'_eq.trans h_e₂'_eq.symm
  have h_i12' : eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval =
      eqToHom h_img2'_obj ≫ toSimplexCategory.map c₂.eval :=
    h_i'_eq.trans h_i₂'_eq.symm
  -- proof-irrelevance for the transported image equalities
  have h_img_obj_eq : h_img1_obj = h_img2'_obj := Subsingleton.elim _ _
  have h_iso_symm_eq : eqToHom h_img1_obj.symm = eqToHom h_img2'_obj.symm := by
    rw [h_img_obj_eq]
  have h_iso_eq : eqToHom h_img1_obj = eqToHom h_img2'_obj := by
    rw [h_img_obj_eq]
  have h_map_e : toSimplexCategory.map e₁ = toSimplexCategory.map e₂ := by
    have h_eq : toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm =
        toSimplexCategory.map e₂ ≫ eqToHom h_img1_obj.symm := by
      calc toSimplexCategory.map e₁ ≫ eqToHom h_img1_obj.symm
          = toSimplexCategory.map e₂ ≫ eqToHom h_img2'_obj.symm := h_e12'
        _ = toSimplexCategory.map e₂ ≫ eqToHom h_img1_obj.symm := by rw [h_iso_symm_eq]
    exact (cancel_mono (eqToHom h_img1_obj.symm)).mp h_eq
  have h_map_c : toSimplexCategory.map c₁.eval = toSimplexCategory.map c₂.eval := by
    have h_eq : eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval =
        eqToHom h_img1_obj ≫ toSimplexCategory.map c₂.eval := by
      calc eqToHom h_img1_obj ≫ toSimplexCategory.map c₁.eval
          = eqToHom h_img2'_obj ≫ toSimplexCategory.map c₂.eval := h_i12'
        _ = eqToHom h_img1_obj ≫ toSimplexCategory.map c₂.eval := by rw [h_iso_eq]
    exact (cancel_epi (eqToHom h_img1_obj)).mp h_eq
  have h_e_eq : e₁ = e₂ :=
    eq_of_toSimplexCategory_map_eq_of_P_sigma he₁ he₂ h_map_e
  have h_c_eq : c₁ = c₂ :=
    DeltaChain.Admissible.eq_of_toSimplexCategory_map_eq hc₁ hc₂ h_map_c
  calc f = e₁ ≫ c₁.eval := hf_eq
    _ = e₂ ≫ c₂.eval := by rw [h_e_eq, h_c_eq]
    _ = g := hg_eq.symm

end Faithfulness

section FullInstance

/--
Fullness of `toSimplexCategory` for arbitrary presented objects,
reduced to the canonical case via boundary `ext` transports.
The inner construction stays canonical; only the outer boundary uses
object equalities.
-/
instance : Functor.Full toSimplexCategory where
  map_surjective := by
    intro X Y θ
    have hx : ∃ n, X = mk n := ⟨X.len, by apply ext; simp [mk_len]⟩
    have hy : ∃ m, Y = mk m := ⟨Y.len, by apply ext; simp [mk_len]⟩
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := hy
    obtain ⟨f, hf⟩ := exists_preimage θ
    exact ⟨f, hf⟩

end FullInstance

section FaithfulInstance

/--
Faithfulness of `toSimplexCategory` for arbitrary presented objects,
reduced to the canonical case via object induction.
-/
instance : Functor.Faithful toSimplexCategory where
  map_injective := by
    intro X Y f g h
    induction X using SimplexCategoryGenRel.rec
    induction Y using SimplexCategoryGenRel.rec
    exact eq_of_toSimplexCategory_map_eq h

end FaithfulInstance

section EssSurjInstance

/--
Essential surjectivity of `toSimplexCategory`: every simplex is isomorphic to a
canonical presented object via `SimplexCategory.ext`.
-/
instance : Functor.EssSurj toSimplexCategory where
  mem_essImage Y := by
    refine ⟨mk Y.len, ⟨?_⟩⟩
    have h : toSimplexCategory.obj (mk Y.len) = Y := by
      apply SimplexCategory.ext
      rfl
    exact eqToIso h

end EssSurjInstance

section IsEquivalenceInstance

instance : Functor.IsEquivalence toSimplexCategory where

end IsEquivalenceInstance

/-- Equivalence `SimplexCategoryGenRel ≌ SimplexCategory`. -/
noncomputable def equivalence : SimplexCategoryGenRel ≌ SimplexCategory :=
  toSimplexCategory.asEquivalence

section FromSimplexCategory

/--
Canonical object equality `toSimplexCategory.obj (mk Δ.len) = Δ`. Both sides are
definitionally `Δ` via `toSimplexCategory_obj_mk` and `mk_len`.
-/
theorem toSimplexCategory_obj_mk_len (Δ : SimplexCategory) :
    toSimplexCategory.obj (mk Δ.len) = Δ :=
  rfl

/-- Canonical isomorphism `toSimplexCategory.obj (mk Δ.len) ≅ Δ`. -/
noncomputable def toSimplexCategory_objIso (Δ : SimplexCategory) :
    toSimplexCategory.obj (mk Δ.len) ≅ Δ :=
  eqToIso (toSimplexCategory_obj_mk_len Δ)

@[simp]
lemma toSimplexCategory_objIso_hom (Δ : SimplexCategory) :
    (toSimplexCategory_objIso Δ).hom = eqToHom (toSimplexCategory_obj_mk_len Δ) :=
  rfl

@[simp]
lemma toSimplexCategory_objIso_inv (Δ : SimplexCategory) :
    (toSimplexCategory_objIso Δ).inv = eqToHom (toSimplexCategory_obj_mk_len Δ).symm :=
  rfl

/--
Explicit inverse-direction functor with canonical objects definitionally visible.
Object is definitionally `mk Δ.len`. Morphism uses fullness via `preimage` after
conjugating by the canonical equality at the boundary. Since the canonical
equality is `rfl`, `eqToHom` is definitionally `𝟙` and the conjugation is trivial;
we keep the `eqToHom` form to match the required interface. Functor laws follow
from faithfulness via `map_injective`.
-/
noncomputable def fromSimplexCategory : SimplexCategory ⥤ SimplexCategoryGenRel where
  obj Δ := mk Δ.len
  map {X Y} f :=
    toSimplexCategory.preimage
      (eqToHom (toSimplexCategory_obj_mk_len X) ≫ f ≫
        eqToHom (toSimplexCategory_obj_mk_len Y).symm)
  map_id X := by
    apply toSimplexCategory.map_injective
    rw [CategoryTheory.Functor.map_preimage]
    rw [CategoryTheory.Functor.map_id]
    have h_cancel :
        eqToHom (toSimplexCategory_obj_mk_len X) ≫
          eqToHom (toSimplexCategory_obj_mk_len X).symm =
          𝟙 (toSimplexCategory.obj (mk X.len)) := by
      rw [eqToHom_trans]
      rfl
    calc
      eqToHom (toSimplexCategory_obj_mk_len X) ≫ 𝟙 X ≫
          eqToHom (toSimplexCategory_obj_mk_len X).symm
        = (eqToHom (toSimplexCategory_obj_mk_len X) ≫ 𝟙 X) ≫
          eqToHom (toSimplexCategory_obj_mk_len X).symm := by
        rfl
      _ = eqToHom (toSimplexCategory_obj_mk_len X) ≫
          eqToHom (toSimplexCategory_obj_mk_len X).symm := by
        rw [Category.comp_id]
      _ = 𝟙 (toSimplexCategory.obj (mk X.len)) := h_cancel
  map_comp {X Y Z} f g := by
    apply toSimplexCategory.map_injective
    rw [CategoryTheory.Functor.map_comp]
    rw [CategoryTheory.Functor.map_preimage]
    rw [CategoryTheory.Functor.map_preimage]
    rw [CategoryTheory.Functor.map_preimage]
    have hY :
        eqToHom (toSimplexCategory_obj_mk_len Y).symm ≫
          eqToHom (toSimplexCategory_obj_mk_len Y) = 𝟙 Y := by
      rw [eqToHom_trans]
      rfl
    calc
      eqToHom (toSimplexCategory_obj_mk_len X) ≫ (f ≫ g) ≫
          eqToHom (toSimplexCategory_obj_mk_len Z).symm
        = eqToHom (toSimplexCategory_obj_mk_len X) ≫ f ≫ g ≫
          eqToHom (toSimplexCategory_obj_mk_len Z).symm := by
        simp only [Category.assoc]
      _ = eqToHom (toSimplexCategory_obj_mk_len X) ≫ f ≫ (𝟙 Y ≫ g) ≫
          eqToHom (toSimplexCategory_obj_mk_len Z).symm := by
        simp only [Category.id_comp]
      _ = eqToHom (toSimplexCategory_obj_mk_len X) ≫ f ≫
          ((eqToHom (toSimplexCategory_obj_mk_len Y).symm ≫
            eqToHom (toSimplexCategory_obj_mk_len Y)) ≫ g) ≫
          eqToHom (toSimplexCategory_obj_mk_len Z).symm := by
        rw [hY]
      _ = (eqToHom (toSimplexCategory_obj_mk_len X) ≫ f ≫
          eqToHom (toSimplexCategory_obj_mk_len Y).symm) ≫
        (eqToHom (toSimplexCategory_obj_mk_len Y) ≫ g ≫
          eqToHom (toSimplexCategory_obj_mk_len Z).symm) := by
        simp only [Category.assoc]

@[simp]
lemma fromSimplexCategory_obj (Δ : SimplexCategory) :
    fromSimplexCategory.obj Δ = mk Δ.len :=
  rfl

@[simp]
lemma fromSimplexCategory_obj_len (Δ : SimplexCategory) :
    (fromSimplexCategory.obj Δ).len = Δ.len :=
  rfl

@[simp]
lemma toSimplexCategory_obj_fromSimplexCategory_obj (Δ : SimplexCategory) :
    toSimplexCategory.obj (fromSimplexCategory.obj Δ) = Δ :=
  rfl

@[simp]
lemma fromSimplexCategory_map_preimage {X Y : SimplexCategory}
    (f : X ⟶ Y) :
    toSimplexCategory.map (fromSimplexCategory.map f) = f := by
  have h_map :
      toSimplexCategory.map (fromSimplexCategory.map f) =
        eqToHom (toSimplexCategory_obj_mk_len X) ≫ f ≫
          eqToHom (toSimplexCategory_obj_mk_len Y).symm := by
    change toSimplexCategory.map
        (toSimplexCategory.preimage
          (eqToHom (toSimplexCategory_obj_mk_len X) ≫ f ≫
            eqToHom (toSimplexCategory_obj_mk_len Y).symm)) =
        eqToHom (toSimplexCategory_obj_mk_len X) ≫ f ≫
          eqToHom (toSimplexCategory_obj_mk_len Y).symm
    rw [CategoryTheory.Functor.map_preimage]
  rw [h_map]
  have h1 : eqToHom (toSimplexCategory_obj_mk_len X) = 𝟙 X := rfl
  have h2 : eqToHom (toSimplexCategory_obj_mk_len Y).symm = 𝟙 Y := rfl
  rw [h1, h2]
  simp

@[simp]
lemma fromSimplexCategory_map_δ {n : ℕ} (i : Fin (n + 2)) :
    fromSimplexCategory.map (SimplexCategory.δ i) = δ i := by
  have h1 : eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk n)) = 𝟙 _ := rfl
  have h2 : eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk (n + 1))).symm = 𝟙 _ := rfl
  have h_eq : eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk n)) ≫
      SimplexCategory.δ i ≫
      eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk (n + 1))).symm =
      SimplexCategory.δ i := by
    rw [h1, h2]
    simp
  have h_to : SimplexCategory.δ i = toSimplexCategory.map (δ i) := by
    rw [toSimplexCategory_map_δ]
  have h_from : fromSimplexCategory.map (SimplexCategory.δ i) =
      toSimplexCategory.preimage
        (eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk n)) ≫
          SimplexCategory.δ i ≫
          eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk (n + 1))).symm) := rfl
  rw [h_from, h_eq, h_to, CategoryTheory.Functor.preimage_map]

@[simp]
lemma fromSimplexCategory_map_σ {n : ℕ} (i : Fin (n + 1)) :
    fromSimplexCategory.map (SimplexCategory.σ i) = σ i := by
  have h1 : eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk (n + 1))) = 𝟙 _ := rfl
  have h2 : eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk n)).symm = 𝟙 _ := rfl
  have h_eq : eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk (n + 1))) ≫
      SimplexCategory.σ i ≫
      eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk n)).symm =
      SimplexCategory.σ i := by
    rw [h1, h2]
    simp
  have h_to : SimplexCategory.σ i = toSimplexCategory.map (σ i) := by
    rw [toSimplexCategory_map_σ]
  have h_from : fromSimplexCategory.map (SimplexCategory.σ i) =
      toSimplexCategory.preimage
        (eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk (n + 1))) ≫
          SimplexCategory.σ i ≫
          eqToHom (toSimplexCategory_obj_mk_len (SimplexCategory.mk n)).symm) := rfl
  rw [h_from, h_eq, h_to, CategoryTheory.Functor.preimage_map]

end FromSimplexCategory

end SimplexCategoryGenRel
