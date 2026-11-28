/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua and Avocado
-/
module

public import MathlibExt.RepresentationTheory.Homological.NormalizedBar.ShuffleTuples
public import MathlibExt.RepresentationTheory.Homological.NormalizedBar.NativeBar

/-!
# Integral shuffle on full and normalized group-bar modules

Let G be any group. The degreewise ℤ-linear shuffle on underlying
tuple modules multiplies the group-ring coefficients in input order
and sums over (p,q)-shuffles σ with sign sgn(σ).
The output tuple is the input concatenation evaluated at σ⁻¹.

A degenerate input makes every output tuple degenerate, so the operator
descends through the projections to the nonidentity tuple modules.
The descended map is unique with this projection characteristic.
It agrees degreewise with the bar normalization projection and with
the normalization-corrected section, for their stated Type 0 group scope.
The raw tuple operators allow arbitrary group universe v.

-/

@[expose] public section

namespace Rep.NormalizedBar

universe v

open CategoryTheory Limits
open scoped Classical

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
The ℤ-linear shuffle B_p⊗[ℤ]B_q→B_(p+q) takes a pair of
basis symbols with ordered group-ring coefficients u,v to
∑_(σ∈Sh(p,q)) sgn(σ) [I_σ(a,b)]_(uv).
The map is on underlying modules. -/
noncomputable def shuffleLinear (G : Type v) [Group G] (p q : ℕ) :
    TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) := by
  classical
  exact TensorProduct.lift
    (Finsupp.lsum ℤ (fun a : Fin p → G =>
      (Finsupp.lsum ℤ (fun ha : G =>
        LinearMap.toSpanSingleton ℤ
          (((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
            ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G))
          (Finsupp.lsum ℤ (fun b : Fin q → G =>
            (Finsupp.lsum ℤ (fun hb : G =>
              LinearMap.toSpanSingleton ℤ
                ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G)
                (∑ σ ∈ Finset.univ.filter
                    (fun σ : Equiv.Perm (Fin (p + q)) =>
              AlgebraicTopology.EilenbergZilber.IsShuffle (p := p) (q := q) σ),
                  ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
                    Finsupp.single ((Fin.addCases a b) ∘ σ.symm)
                      (MonoidAlgebra.single (ha * hb) (1 : ℤ))))).comp
              (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)))).comp
        (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap))

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
For coefficients c_a[h_a],c_b[h_b], the basis value is
c_a c_b∑_(σ∈Sh(p,q)) sgn(σ)
[I_σ(a,b)]_[h_a h_b].
The group entries h_a,h_b are multiplied in their input order. -/
theorem shuffleLinear_basis (G : Type v) [Group G] (p q : ℕ)
    (a : Fin p → G) (b : Fin q → G) (ha hb : G) (ca cb : ℤ) :
    shuffleLinear G p q
        (Finsupp.single a (MonoidAlgebra.single ha ca) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb cb)) =
      (ca * cb) •
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (p + q)) =>
              AlgebraicTopology.EilenbergZilber.IsShuffle (p := p) (q := q) σ),
          ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
            Finsupp.single (Rep.NormalizedBar.interleave a b σ)
              (MonoidAlgebra.single (ha * hb) (1 : ℤ)) := by
  classical
  let W (aa : Fin p → G) (hh : G) (bb : Fin q → G) (kk : G) :
      (Fin (p + q) → G) →₀ MonoidAlgebra ℤ G :=
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (p + q)) =>
              AlgebraicTopology.EilenbergZilber.IsShuffle (p := p) (q := q) σ),
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        Finsupp.single ((Fin.addCases aa bb) ∘ σ.symm)
          (MonoidAlgebra.single (hh * kk) (1 : ℤ))
  let E : MonoidAlgebra ℤ G →ₗ[ℤ] G →₀ ℤ :=
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap
  let rightScalar (aa : Fin p → G) (hh : G) (bb : Fin q → G) :
      G → ℤ →ₗ[ℤ] ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) :=
    fun kk => LinearMap.toSpanSingleton ℤ
      ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) (W aa hh bb kk)
  let rightTuple (aa : Fin p → G) (hh : G) :
      (Fin q → G) → MonoidAlgebra ℤ G →ₗ[ℤ]
        ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) :=
    fun bb => (Finsupp.lsum ℤ (rightScalar aa hh bb)).comp E
  let Q (aa : Fin p → G) (hh : G) :
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) :=
    Finsupp.lsum ℤ (rightTuple aa hh)
  let leftScalar (aa : Fin p → G) :
      G → ℤ →ₗ[ℤ]
        (((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
          ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G)) :=
    fun hh => LinearMap.toSpanSingleton ℤ
      (((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G)) (Q aa hh)
  let leftTuple : (Fin p → G) → MonoidAlgebra ℤ G →ₗ[ℤ]
      (((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G)) :=
    fun aa => (Finsupp.lsum ℤ (leftScalar aa)).comp E
  let B : ((Fin p → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G)) :=
    Finsupp.lsum ℤ leftTuple
  have hcoeff (h : G) (c : ℤ) : E (MonoidAlgebra.single h c) =
      Finsupp.single h c := rfl
  have hrightTuple (aa : Fin p → G) (hh : G) (bb : Fin q → G) (kk : G) (c : ℤ) :
      rightTuple aa hh bb (MonoidAlgebra.single kk c) = c • W aa hh bb kk := by
    change (Finsupp.lsum ℤ (rightScalar aa hh bb)) (E (MonoidAlgebra.single kk c)) = _
    calc
      _ = (Finsupp.lsum ℤ (rightScalar aa hh bb)) (Finsupp.single kk c) :=
        congrArg (Finsupp.lsum ℤ (rightScalar aa hh bb)) (hcoeff kk c)
      _ = rightScalar aa hh bb kk c :=
        Finsupp.lsum_single (R := ℤ) (R₂ := ℤ) (S := ℤ) (σ := RingHom.id ℤ)
          (f := rightScalar aa hh bb) (i := kk) (m := c)
      _ = c • W aa hh bb kk :=
        LinearMap.toSpanSingleton_apply ℤ
          ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) (W aa hh bb kk) c
  have hQ (aa : Fin p → G) (hh : G) :
      Q aa hh (Finsupp.single b (MonoidAlgebra.single hb cb)) = cb • W aa hh b hb :=
    (Finsupp.lsum_single (R := ℤ) (R₂ := ℤ) (S := ℤ) (σ := RingHom.id ℤ)
      (f := rightTuple aa hh) (i := b) (m := MonoidAlgebra.single hb cb)).trans
        (hrightTuple aa hh b hb cb)
  have hleftTuple : leftTuple a (MonoidAlgebra.single ha ca) = ca • Q a ha := by
    change (Finsupp.lsum ℤ (leftScalar a)) (E (MonoidAlgebra.single ha ca)) = _
    calc
      _ = (Finsupp.lsum ℤ (leftScalar a)) (Finsupp.single ha ca) :=
        congrArg (Finsupp.lsum ℤ (leftScalar a)) (hcoeff ha ca)
      _ = leftScalar a ha ca :=
        Finsupp.lsum_single (R := ℤ) (R₂ := ℤ) (S := ℤ) (σ := RingHom.id ℤ)
          (f := leftScalar a) (i := ha) (m := ca)
      _ = ca • Q a ha :=
        LinearMap.toSpanSingleton_apply ℤ
          (((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
            ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G)) (Q a ha) ca
  have hB : B (Finsupp.single a (MonoidAlgebra.single ha ca)) = ca • Q a ha :=
    (Finsupp.lsum_single (R := ℤ) (R₂ := ℤ) (S := ℤ) (σ := RingHom.id ℤ)
      (f := leftTuple) (i := a) (m := MonoidAlgebra.single ha ca)).trans hleftTuple
  change TensorProduct.lift B
      (Finsupp.single a (MonoidAlgebra.single ha ca) ⊗ₜ[ℤ]
        Finsupp.single b (MonoidAlgebra.single hb cb)) = (ca * cb) • W a ha b hb
  calc
    _ = B (Finsupp.single a (MonoidAlgebra.single ha ca))
        (Finsupp.single b (MonoidAlgebra.single hb cb)) :=
      TensorProduct.lift.tmul (R := ℤ) (σ₁₂ := RingHom.id ℤ) (f' := B)
        (x := Finsupp.single a (MonoidAlgebra.single ha ca))
        (y := Finsupp.single b (MonoidAlgebra.single hb cb))
    _ = (ca • Q a ha) (Finsupp.single b (MonoidAlgebra.single hb cb)) :=
      congrArg (fun F : ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) =>
          F (Finsupp.single b (MonoidAlgebra.single hb cb))) hB
    _ = ca • Q a ha (Finsupp.single b (MonoidAlgebra.single hb cb)) :=
      LinearMap.smul_apply ca (Q a ha) (Finsupp.single b (MonoidAlgebra.single hb cb))
    _ = ca • (cb • W a ha b hb) :=
      congrArg (fun z : (Fin (p + q) → G) →₀ MonoidAlgebra ℤ G => ca • z) (hQ a ha)
    _ = (ca * cb) • W a ha b hb := (mul_smul ca cb (W a ha b hb)).symm

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
The normalized ℤ-linear operator Q_p⊗[ℤ]Q_q→Q_(p+q)
is obtained by including nonidentity tuples, applying the full
shuffle and projecting the output to nonidentity tuples. -/
noncomputable def normalizedShuffleLinear (G : Type v) [Group G] (p q : ℕ) :
    TensorProduct ℤ ((Rep.NormalizedBar.complex ℤ G).X p).V
      ((Rep.NormalizedBar.complex ℤ G).X q).V →ₗ[ℤ]
      ((Rep.NormalizedBar.complex ℤ G).X (p + q)).V :=
  (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap.comp
    ((shuffleLinear G p q).comp
      (TensorProduct.map (Rep.NormalizedBar.rawInclusion ℤ G p).hom.toLinearMap
        (Rep.NormalizedBar.rawInclusion ℤ G q).hom.toLinearMap))

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
If a has an identity entry, the output of its full shuffle with b
is killed by the degree p+q nonidentity projection. -/
theorem shuffle_projection_zero_of_degenerate_left (G : Type v) [Group G] (p q : ℕ)
    (a : Fin p → G) (b : Fin q → G) (ha hb : G)
    (hdeg : ¬ Rep.NormalizedBar.IsNondegenerate G a) :
    (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom
      (shuffleLinear G p q
        (Finsupp.single a (MonoidAlgebra.single ha 1) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb 1))) = 0 := by
  classical
  rw [shuffleLinear_basis]
  simp only [one_mul, one_smul, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro σ hσ
  have h := Rep.NormalizedBar.interleave_degenerate_left a b σ hdeg
  have hp := Rep.NormalizedBar.rawProjection_single_single ℤ G (p + q)
    (Rep.NormalizedBar.interleave a b σ) (ha * hb) (1 : ℤ)
  rw [dite_eq_right h] at hp
  rw [hp, smul_zero]

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
If b has an identity entry, the output of its full shuffle with a
is killed by the degree p+q nonidentity projection. -/
theorem shuffle_projection_zero_of_degenerate_right (G : Type v) [Group G] (p q : ℕ)
    (a : Fin p → G) (b : Fin q → G) (ha hb : G)
    (hdeg : ¬ Rep.NormalizedBar.IsNondegenerate G b) :
    (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom
      (shuffleLinear G p q
        (Finsupp.single a (MonoidAlgebra.single ha 1) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb 1))) = 0 := by
  classical
  rw [shuffleLinear_basis]
  simp only [one_mul, one_smul, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro σ hσ
  have h := Rep.NormalizedBar.interleave_degenerate_right a b σ hdeg
  have hp := Rep.NormalizedBar.rawProjection_single_single ℤ G (p + q)
    (Rep.NormalizedBar.interleave a b σ) (ha * hb) (1 : ℤ)
  rw [dite_eq_right h] at hp
  rw [hp, smul_zero]

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
For full and normalized shuffles S and S̄ and projections π_n,
S̄∘(π_p⊗π_q)=π_(p+q)∘S. -/
theorem normalizedShuffleLinear_desc (G : Type v) [Group G] (p q : ℕ) :
    (normalizedShuffleLinear G p q).comp
        (TensorProduct.map (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
          (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap) =
      (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap.comp
        (shuffleLinear G p q) := by
  classical
  let S : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) := shuffleLinear G p q
  let N : TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
      (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) :=
    normalizedShuffleLinear G p q
  let P : ((Fin p → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
  let Q : ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap
  let O : ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap
  let Jp : (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      ((Fin p → G) →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawInclusion ℤ G p).hom.toLinearMap
  let Jq : (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawInclusion ℤ G q).hom.toLinearMap
  change N.comp (TensorProduct.map P Q) = O.comp S
  apply TensorProduct.ext
  apply Finsupp.lhom_ext'
  intro a
  apply MonoidAlgebra.lhom_ext'
  intro ha
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro b
  apply MonoidAlgebra.lhom_ext'
  intro hb
  apply LinearMap.ext_ring
  change N
      (TensorProduct.map P Q
        (Finsupp.single a (MonoidAlgebra.single ha 1) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb 1))) =
    O
      (S
        (Finsupp.single a (MonoidAlgebra.single ha 1) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb 1)))
  rw [TensorProduct.map_tmul]
  by_cases hA : Rep.NormalizedBar.IsNondegenerate G a
  · have hpa : P
        (Finsupp.single a (MonoidAlgebra.single ha 1)) =
        Finsupp.single ⟨a, hA⟩ (MonoidAlgebra.single ha 1) := by
      have h := Rep.NormalizedBar.rawProjection_single_single ℤ G p a ha (1 : ℤ)
      rw [dite_eq_left hA] at h
      exact h
    rw [hpa]
    by_cases hB : Rep.NormalizedBar.IsNondegenerate G b
    · have hpb : Q
          (Finsupp.single b (MonoidAlgebra.single hb 1)) =
          Finsupp.single ⟨b, hB⟩ (MonoidAlgebra.single hb 1) := by
        have h := Rep.NormalizedBar.rawProjection_single_single ℤ G q b hb (1 : ℤ)
        rw [dite_eq_left hB] at h
        exact h
      rw [hpb]
      change O
          (S
            (TensorProduct.map Jp Jq
              (Finsupp.single ⟨a, hA⟩ (MonoidAlgebra.single ha 1) ⊗ₜ[ℤ]
                Finsupp.single ⟨b, hB⟩ (MonoidAlgebra.single hb 1)))) = _
      rw [TensorProduct.map_tmul]
      have hJa : Jp (Finsupp.single ⟨a, hA⟩ (MonoidAlgebra.single ha 1)) =
          Finsupp.single a (MonoidAlgebra.single ha 1) :=
        Rep.NormalizedBar.rawInclusion_single_single ℤ G p ⟨a, hA⟩ ha 1
      have hJb : Jq (Finsupp.single ⟨b, hB⟩ (MonoidAlgebra.single hb 1)) =
          Finsupp.single b (MonoidAlgebra.single hb 1) :=
        Rep.NormalizedBar.rawInclusion_single_single ℤ G q ⟨b, hB⟩ hb 1
      rw [hJa, hJb]
    · have hpb : Q
          (Finsupp.single b (MonoidAlgebra.single hb 1)) = 0 := by
        have h := Rep.NormalizedBar.rawProjection_single_single ℤ G q b hb (1 : ℤ)
        rw [dite_eq_right hB] at h
        exact h
      rw [hpb, TensorProduct.tmul_zero, N.map_zero]
      exact (shuffle_projection_zero_of_degenerate_right G p q a b ha hb hB).symm
  · have hpa : P
        (Finsupp.single a (MonoidAlgebra.single ha 1)) = 0 := by
      have h := Rep.NormalizedBar.rawProjection_single_single ℤ G p a ha (1 : ℤ)
      rw [dite_eq_right hA] at h
      exact h
    rw [hpa, TensorProduct.zero_tmul, N.map_zero]
    exact (shuffle_projection_zero_of_degenerate_left G p q a b ha hb hA).symm

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
For nonidentity a,b, the normalized basis value is the output
projection of
c_a c_b∑_(σ∈Sh(p,q))sgn(σ)[I_σ(a,b)]_[h_a h_b]. -/
theorem normalizedShuffleLinear_basis (G : Type v) [Group G] (p q : ℕ)
    (a : Rep.NormalizedBar.Tuple G p) (b : Rep.NormalizedBar.Tuple G q)
    (ha hb : G) (ca cb : ℤ) :
    normalizedShuffleLinear G p q
        (Finsupp.single a (MonoidAlgebra.single ha ca) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb cb)) =
      (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom
        ((ca * cb) •
          ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (p + q)) =>
              AlgebraicTopology.EilenbergZilber.IsShuffle (p := p) (q := q) σ),
            ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
              Finsupp.single (Rep.NormalizedBar.interleave a.val b.val σ)
                (MonoidAlgebra.single (ha * hb) (1 : ℤ))) := by
  let S : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) := shuffleLinear G p q
  let P : ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap
  let Jp : (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      ((Fin p → G) →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawInclusion ℤ G p).hom.toLinearMap
  let Jq : (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawInclusion ℤ G q).hom.toLinearMap
  change P (S (TensorProduct.map Jp Jq
      (Finsupp.single a (MonoidAlgebra.single ha ca) ⊗ₜ[ℤ]
        Finsupp.single b (MonoidAlgebra.single hb cb)))) = _
  rw [TensorProduct.map_tmul]
  have hJa : Jp (Finsupp.single a (MonoidAlgebra.single ha ca)) =
      Finsupp.single a.val (MonoidAlgebra.single ha ca) :=
    Rep.NormalizedBar.rawInclusion_single_single ℤ G p a ha ca
  have hJb : Jq (Finsupp.single b (MonoidAlgebra.single hb cb)) =
      Finsupp.single b.val (MonoidAlgebra.single hb cb) :=
    Rep.NormalizedBar.rawInclusion_single_single ℤ G q b hb cb
  rw [hJa, hJb]
  exact congrArg (fun x : (Fin (p + q) → G) →₀ MonoidAlgebra ℤ G => P x)
    (shuffleLinear_basis G p q a.val b.val ha hb ca cb)

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
Every interleaving of nonidentity a,b is nonidentity. Thus the
normalized basis value is directly
c_a c_b∑_(σ∈Sh(p,q))sgn(σ)[I_σ(a,b)]_[h_a h_b]
as a sum of normalized tuple symbols. -/
theorem normalizedShuffleLinear_nonidentity_basis (G : Type v) [Group G] (p q : ℕ)
    (a : Rep.NormalizedBar.Tuple G p) (b : Rep.NormalizedBar.Tuple G q)
    (ha hb : G) (ca cb : ℤ) :
    normalizedShuffleLinear G p q
        (Finsupp.single a (MonoidAlgebra.single ha ca) ⊗ₜ[ℤ]
          Finsupp.single b (MonoidAlgebra.single hb cb)) =
      (ca * cb) •
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (p + q)) =>
              AlgebraicTopology.EilenbergZilber.IsShuffle (p := p) (q := q) σ),
          ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
            Finsupp.single (Rep.NormalizedBar.interleaveTuple a b σ)
              (MonoidAlgebra.single (ha * hb) (1 : ℤ)) := by
  classical
  rw [normalizedShuffleLinear_basis]
  let P : ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) :=
    (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap
  change P ((ca * cb) •
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (p + q)) =>
              AlgebraicTopology.EilenbergZilber.IsShuffle (p := p) (q := q) σ),
        ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
          Finsupp.single (Rep.NormalizedBar.interleave a.val b.val σ)
            (MonoidAlgebra.single (ha * hb) (1 : ℤ))) = _
  rw [P.map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [P.map_smul]
  have hnd : Rep.NormalizedBar.IsNondegenerate G
      (Rep.NormalizedBar.interleave a.val b.val σ) :=
    (Rep.NormalizedBar.isNondegenerate_interleave_iff a.val b.val σ).mpr
      ⟨a.property, b.property⟩
  have hp : P (Finsupp.single (Rep.NormalizedBar.interleave a.val b.val σ)
      (MonoidAlgebra.single (ha * hb) (1 : ℤ))) =
      Finsupp.single (Rep.NormalizedBar.interleaveTuple a b σ)
        (MonoidAlgebra.single (ha * hb) (1 : ℤ)) := by
    have h := Rep.NormalizedBar.rawProjection_single_single ℤ G (p + q)
      (Rep.NormalizedBar.interleave a.val b.val σ) (ha * hb) (1 : ℤ)
    rw [dite_eq_left hnd] at h
    exact h
  rw [hp]

/-- Let G be a group in Type 0 and p,q∈ℕ.
For the inhomogeneous bar projection π_B to normalized tuples,
the integral shuffles satisfy
S̄∘(π_B,p⊗π_B,q)=π_B,p+q∘S. -/
theorem normalizedShuffleLinear_nativeProjection (G : Type) [Group G] (p q : ℕ) :
    (normalizedShuffleLinear G p q).comp
        (TensorProduct.map ((Rep.NormalizedBar.nativeProjection ℤ G).f p).hom.toLinearMap
          ((Rep.NormalizedBar.nativeProjection ℤ G).f q).hom.toLinearMap) =
      ((Rep.NormalizedBar.nativeProjection ℤ G).f (p + q)).hom.toLinearMap.comp
        (shuffleLinear G p q) := by
  let S : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) := shuffleLinear G p q
  let N : TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
      (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) :=
    normalizedShuffleLinear G p q
  let P : ((Fin p → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G) :=
    ((Rep.NormalizedBar.nativeProjection ℤ G).f p).hom.toLinearMap
  let Q : ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) :=
    ((Rep.NormalizedBar.nativeProjection ℤ G).f q).hom.toLinearMap
  let O : ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) :=
    ((Rep.NormalizedBar.nativeProjection ℤ G).f (p + q)).hom.toLinearMap
  have hP : P = (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap :=
    congrArg (fun f : Rep.NormalizedBar.fullDegree ℤ G p ⟶ Rep.NormalizedBar.degree ℤ G p =>
      f.hom.toLinearMap) (Rep.NormalizedBar.nativeProjection_f ℤ G p)
  have hQ : Q = (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap :=
    congrArg (fun f : Rep.NormalizedBar.fullDegree ℤ G q ⟶ Rep.NormalizedBar.degree ℤ G q =>
      f.hom.toLinearMap) (Rep.NormalizedBar.nativeProjection_f ℤ G q)
  have hO : O = (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap :=
    congrArg (fun f : Rep.NormalizedBar.fullDegree ℤ G (p + q) ⟶
      Rep.NormalizedBar.degree ℤ G (p + q) => f.hom.toLinearMap)
        (Rep.NormalizedBar.nativeProjection_f ℤ G (p + q))
  change N.comp (TensorProduct.map P Q) = O.comp S
  have hMap : TensorProduct.map P Q =
      TensorProduct.map (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
        (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap :=
    congrArg₂
      (fun (f : ((Fin p → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
            (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G))
          (g : ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
            (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G)) => TensorProduct.map f g)
      hP hQ
  have hLeft : N.comp (TensorProduct.map P Q) = N.comp
      (TensorProduct.map (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
        (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap) :=
    congrArg
      (fun f : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
          ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
          TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
            (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) => N.comp f) hMap
  have hDesc : N.comp
      (TensorProduct.map (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
        (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap) =
      (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap.comp S :=
    normalizedShuffleLinear_desc G p q
  have hRight : (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap.comp S =
      O.comp S :=
    congrArg
      (fun f : ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
          (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) => f.comp S) hO.symm
  exact hLeft.trans (hDesc.trans hRight)

/-- Let G be a group in Type 0 and p,q∈ℕ.
For the bar normalization projection π_B and corrected chain
section i_B, the normalized underlying-module shuffle is
S̄=π_B,p+q∘S∘(i_B,p⊗i_B,q). -/
theorem normalizedShuffleLinear_nativeInclusion (G : Type) [Group G] (p q : ℕ) :
    normalizedShuffleLinear G p q =
      ((Rep.NormalizedBar.nativeProjection ℤ G).f (p + q)).hom.toLinearMap.comp
        ((shuffleLinear G p q).comp
          (TensorProduct.map ((Rep.NormalizedBar.nativeInclusion ℤ G).f p).hom.toLinearMap
            ((Rep.NormalizedBar.nativeInclusion ℤ G).f q).hom.toLinearMap)) := by
  let Q : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
        (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) :=
    TensorProduct.map ((Rep.NormalizedBar.nativeProjection ℤ G).f p).hom.toLinearMap
      ((Rep.NormalizedBar.nativeProjection ℤ G).f q).hom.toLinearMap
  let I : TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
      (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
        ((Fin q → G) →₀ MonoidAlgebra ℤ G) :=
    TensorProduct.map ((Rep.NormalizedBar.nativeInclusion ℤ G).f p).hom.toLinearMap
      ((Rep.NormalizedBar.nativeInclusion ℤ G).f q).hom.toLinearMap
  let P : ((Fin (p + q) → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) :=
    ((Rep.NormalizedBar.nativeProjection ℤ G).f (p + q)).hom.toLinearMap
  have hSection (n : ℕ) (x : (Rep.NormalizedBar.Tuple G n →₀ MonoidAlgebra ℤ G)) :
      ((Rep.NormalizedBar.nativeProjection ℤ G).f n).hom
        (((Rep.NormalizedBar.nativeInclusion ℤ G).f n).hom x) = x :=
    congrArg (fun f : Rep.NormalizedBar.complex ℤ G ⟶ Rep.NormalizedBar.complex ℤ G =>
      (f.f n).hom x) (Rep.NormalizedBar.nativeInclusion_comp_nativeProjection ℤ G)
  have hQI : Q.comp I = LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    let Pp : ((Fin p → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G) :=
      ((Rep.NormalizedBar.nativeProjection ℤ G).f p).hom.toLinearMap
    let Pq : ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) :=
      ((Rep.NormalizedBar.nativeProjection ℤ G).f q).hom.toLinearMap
    let Ip : (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin p → G) →₀ MonoidAlgebra ℤ G) :=
      ((Rep.NormalizedBar.nativeInclusion ℤ G).f p).hom.toLinearMap
    let Iq : (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin q → G) →₀ MonoidAlgebra ℤ G) :=
      ((Rep.NormalizedBar.nativeInclusion ℤ G).f q).hom.toLinearMap
    have hComp : (Q.comp I) (x ⊗ₜ[ℤ] y) = Q (I (x ⊗ₜ[ℤ] y)) := rfl
    have hI : I (x ⊗ₜ[ℤ] y) = Ip x ⊗ₜ[ℤ] Iq y :=
      TensorProduct.map_tmul Ip Iq x y
    have hQ : Q (Ip x ⊗ₜ[ℤ] Iq y) = Pp (Ip x) ⊗ₜ[ℤ] Pq (Iq y) :=
      TensorProduct.map_tmul Pp Pq (Ip x) (Iq y)
    have hp : Pp (Ip x) = x := hSection p x
    have hq : Pq (Iq y) = y := hSection q y
    have hTensor : Pp (Ip x) ⊗ₜ[ℤ] Pq (Iq y) = x ⊗ₜ[ℤ] y := congrArg₂
      (fun (a : Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
          (b : Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) => a ⊗ₜ[ℤ] b) hp hq
    exact hComp.trans ((congrArg
      (fun z : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
          ((Fin q → G) →₀ MonoidAlgebra ℤ G) => Q z) hI).trans
        (hQ.trans hTensor))
  have hDesc : (normalizedShuffleLinear G p q).comp Q = P.comp (shuffleLinear G p q) :=
    normalizedShuffleLinear_nativeProjection G p q
  have h : ((normalizedShuffleLinear G p q).comp Q).comp I =
      (P.comp (shuffleLinear G p q)).comp I :=
    congrArg
      (fun F : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
          ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
          (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) => F.comp I) hDesc
  have hleft : ((normalizedShuffleLinear G p q).comp Q).comp I =
      normalizedShuffleLinear G p q :=
    (LinearMap.comp_assoc I Q (normalizedShuffleLinear G p q)).trans
      ((congrArg
        (fun F : TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
            (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
            TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
              (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) =>
          (normalizedShuffleLinear G p q).comp F) hQI).trans (by rfl))
  change normalizedShuffleLinear G p q = P.comp ((shuffleLinear G p q).comp I)
  exact hleft.symm.trans (h.trans (LinearMap.comp_assoc I (shuffleLinear G p q) P))

/-- Let G be a group in universe v and p,q∈ℕ.
Let B_n=(G^n→₀ℤ[G]) and Q_n=(N_n→₀ℤ[G]), with N_n the
nonidentity tuples. For a permutation σ of p+q positions,
I_σ(a,b) is concatenation evaluated at σ⁻¹.
If an ℤ-linear F:Q_p⊗Q_q→Q_(p+q) satisfies
F∘(π_p⊗π_q)=π_(p+q)∘S, then F=S̄.
This is the uniqueness characteristic of the descended shuffle. -/
theorem normalizedShuffleLinear_unique (G : Type v) [Group G] (p q : ℕ)
    (F : TensorProduct ℤ ((Rep.NormalizedBar.complex ℤ G).X p).V
      ((Rep.NormalizedBar.complex ℤ G).X q).V →ₗ[ℤ]
        ((Rep.NormalizedBar.complex ℤ G).X (p + q)).V)
    (hF : F.comp
        (TensorProduct.map (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
          (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap) =
      (Rep.NormalizedBar.rawProjection ℤ G (p + q)).hom.toLinearMap.comp
        (shuffleLinear G p q)) :
    F = normalizedShuffleLinear G p q := by
  let Q : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
      ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
        (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) :=
    TensorProduct.map (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
      (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap
  let J : TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
      (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
        ((Fin q → G) →₀ MonoidAlgebra ℤ G) :=
    TensorProduct.map (Rep.NormalizedBar.rawInclusion ℤ G p).hom.toLinearMap
      (Rep.NormalizedBar.rawInclusion ℤ G q).hom.toLinearMap
  have hSection (n : ℕ) (x : (Rep.NormalizedBar.Tuple G n →₀ MonoidAlgebra ℤ G)) :
      (Rep.NormalizedBar.rawProjection ℤ G n).hom
        ((Rep.NormalizedBar.rawInclusion ℤ G n).hom x) = x :=
    congrArg (fun f : Rep.NormalizedBar.degree ℤ G n ⟶ Rep.NormalizedBar.degree ℤ G n =>
      f.hom x) (Rep.NormalizedBar.rawInclusion_comp_rawProjection ℤ G n)
  have hQJ : Q.comp J = LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    let Pp : ((Fin p → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G) :=
      (Rep.NormalizedBar.rawProjection ℤ G p).hom.toLinearMap
    let Pq : ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) :=
      (Rep.NormalizedBar.rawProjection ℤ G q).hom.toLinearMap
    let Jp : (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin p → G) →₀ MonoidAlgebra ℤ G) :=
      (Rep.NormalizedBar.rawInclusion ℤ G p).hom.toLinearMap
    let Jq : (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
        ((Fin q → G) →₀ MonoidAlgebra ℤ G) :=
      (Rep.NormalizedBar.rawInclusion ℤ G q).hom.toLinearMap
    change TensorProduct.map Pp Pq (TensorProduct.map Jp Jq (x ⊗ₜ[ℤ] y)) = x ⊗ₜ[ℤ] y
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
    have hp : Pp (Jp x) = x := hSection p x
    have hq : Pq (Jq y) = y := hSection q y
    exact congrArg₂
      (fun (a : Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
          (b : Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) => a ⊗ₜ[ℤ] b) hp hq
  have h : F.comp Q = (normalizedShuffleLinear G p q).comp Q :=
    hF.trans (normalizedShuffleLinear_desc G p q).symm
  have hJ : (F.comp Q).comp J = ((normalizedShuffleLinear G p q).comp Q).comp J :=
    congrArg
      (fun K : TensorProduct ℤ ((Fin p → G) →₀ MonoidAlgebra ℤ G)
          ((Fin q → G) →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
          (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G) => K.comp J) h
  have collapse (K : TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
      (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
      (Rep.NormalizedBar.Tuple G (p + q) →₀ MonoidAlgebra ℤ G)) :
      (K.comp Q).comp J = K :=
    (LinearMap.comp_assoc J Q K).trans
      ((congrArg
        (fun H : TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
            (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) →ₗ[ℤ]
            TensorProduct ℤ (Rep.NormalizedBar.Tuple G p →₀ MonoidAlgebra ℤ G)
              (Rep.NormalizedBar.Tuple G q →₀ MonoidAlgebra ℤ G) => K.comp H) hQJ).trans
        (by rfl))
  exact (collapse F).symm.trans (hJ.trans (collapse (normalizedShuffleLinear G p q)))


end Rep.NormalizedBar
