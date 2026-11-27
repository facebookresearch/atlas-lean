/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.QuadraticForm.HalfDimensionalTotallyIsotropic

/-!
# Round forms and binary Pfister factors

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Roundness means that,
for every nonzero c, c is represented by Q if and only if cQ is isometric to Q. Roundness is
invariant under isometry. If Q is round and c ≠ 0, the form (x,y) ↦ Q(x) − cQ(y) on V × V is
round. Both results apply to arbitrary vector spaces over fields of any characteristic.

## Reference

* R. Elman, N. Karpenko, A. Merkurjev,   *The Algebraic and Geometric Theory of Quadratic
Forms*, Proposition 9.8.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace QuadraticMap.IsRound

variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]

private def binaryMulLinearMap (c p q : F) :
    (V × V) →ₗ[F] (V × V) :=
  (((p • LinearMap.fst F V V) +
      ((c * q) • LinearMap.snd F V V)).prod
    ((q • LinearMap.fst F V V) +
      (p • LinearMap.snd F V V)))

@[simp]
private theorem binaryMulLinearMap_apply (c p q : F) (x y : V) :
    binaryMulLinearMap (V := V) c p q (x, y) =
      (p • x + (c * q) • y, q • x + p • y) :=
  rfl

private def binaryMulInverseLinearMap (c p q d : F) :
    (V × V) →ₗ[F] (V × V) :=
  ((((d⁻¹ * p) • LinearMap.fst F V V) +
      ((-(d⁻¹ * c * q)) • LinearMap.snd F V V)).prod
    (((-(d⁻¹ * q)) • LinearMap.fst F V V) +
      ((d⁻¹ * p) • LinearMap.snd F V V)))

@[simp]
private theorem binaryMulInverseLinearMap_apply
    (c p q d : F) (x y : V) :
    binaryMulInverseLinearMap (V := V) c p q d (x, y) =
      ((d⁻¹ * p) • x + (-(d⁻¹ * c * q)) • y,
        (-(d⁻¹ * q)) • x + (d⁻¹ * p) • y) :=
  rfl

private noncomputable def binaryMulLinearEquiv
    (c p q : F) (hd : p * p - c * (q * q) ≠ 0) :
    (V × V) ≃ₗ[F] (V × V) := by
  let d := p * p - c * (q * q)
  let f := binaryMulLinearMap (V := V) c p q
  let g := binaryMulInverseLinearMap (V := V) c p q d
  have hd₂ : p ^ 2 - c * q ^ 2 ≠ 0 := by
    simpa [pow_two] using hd
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · apply LinearMap.ext
    rintro ⟨x, y⟩
    ext <;> simp only [f, g, d, LinearMap.comp_apply,
      binaryMulLinearMap_apply, binaryMulInverseLinearMap_apply,
      LinearMap.id_apply]
    all_goals module_nf
    · conv_rhs => rw [← one_smul F x]
      congr 1
      calc
        _ = (p ^ 2 - c * q ^ 2) * (p ^ 2 - c * q ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ hd₂
    · conv_rhs => rw [← one_smul F y]
      congr 1
      calc
        _ = (p ^ 2 - c * q ^ 2) * (p ^ 2 - c * q ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ hd₂
  · apply LinearMap.ext
    rintro ⟨x, y⟩
    ext <;> simp only [f, g, d, LinearMap.comp_apply,
      binaryMulLinearMap_apply, binaryMulInverseLinearMap_apply,
      LinearMap.id_apply]
    all_goals module_nf
    · conv_rhs => rw [← one_smul F x]
      congr 1
      calc
        _ = (p ^ 2 - c * q ^ 2) * (p ^ 2 - c * q ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ hd₂
    · conv_rhs => rw [← one_smul F y]
      congr 1
      calc
        _ = (p ^ 2 - c * q ^ 2) * (p ^ 2 - c * q ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ hd₂

@[simp]
private theorem binaryMulLinearEquiv_apply
    (c p q : F) (hd : p * p - c * (q * q) ≠ 0) (x y : V) :
    binaryMulLinearEquiv (V := V) c p q hd (x, y) =
      (p • x + (c * q) • y, q • x + p • y) :=
  rfl

private noncomputable def binaryMulIsometryEquiv
    (Q : QuadraticForm F V) (c p q : F)
    (hd : p * p - c * (q * q) ≠ 0) :
    ((p * p - c * (q * q)) • (Q.prod ((-c) • Q))).IsometryEquiv
      (Q.prod ((-c) • Q)) where
  toLinearEquiv := binaryMulLinearEquiv (V := V) c p q hd
  map_app' z := by
    rcases z with ⟨x, y⟩
    change Q (p • x + (c * q) • y) +
        (-c • Q) (q • x + p • y) =
      ((p * p - c * (q * q)) • (Q.prod ((-c) • Q))) (x, y)
    simp only [QuadraticMap.prod_apply, smul_apply]
    rw [QuadraticMap.map_add Q (p • x) ((c * q) • y),
      QuadraticMap.map_add Q (q • x) (p • y),
      Q.map_smul, Q.map_smul, Q.map_smul, Q.map_smul,
      Q.polar_smul_left, Q.polar_smul_right,
      Q.polar_smul_left, Q.polar_smul_right]
    simp only [smul_eq_mul]
    ring

private theorem similarity_prod_of_similarity
    (Q : QuadraticForm F V) (c d : F)
    (h : (d • Q).Equivalent Q) :
    (d • (Q.prod ((-c) • Q))).Equivalent
      (Q.prod ((-c) • Q)) := by
  obtain ⟨e⟩ := h
  let ep := e.prod (e.smul (-c))
  have hsource :
      d • (Q.prod ((-c) • Q)) =
        (d • Q).prod ((-c) • (d • Q)) := by
    ext z
    rcases z with ⟨x, y⟩
    simp only [QuadraticMap.prod_apply, smul_apply]
    ring
  exact ⟨(IsometryEquiv.ofEq hsource).trans ep⟩

private theorem similarity_mul
    (P : QuadraticForm F V) (c d : F)
    (hc : (c • P).Equivalent P)
    (hd : (d • P).Equivalent P) :
    ((c * d) • P).Equivalent P := by
  obtain ⟨ec⟩ := hc
  obtain ⟨ed⟩ := hd
  have hsource : (c * d) • P = c • (d • P) := by
    ext x
    simp only [smul_apply]
    ring
  exact ⟨(IsometryEquiv.ofEq hsource).trans ((ed.smul c).trans ec)⟩

private theorem similarity_transport
    {W : Type w} [AddCommGroup W] [Module F W]
    {P : QuadraticForm F V} {P' : QuadraticForm F W}
    (e : P.IsometryEquiv P')
    (d : F) (h : (d • P).Equivalent P) :
    (d • P').Equivalent P' := by
  obtain ⟨ed⟩ := h
  exact ⟨(e.symm.smul d).trans (ed.trans e)⟩

/-- **Isometry invariance of roundness.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Roundness means that,
for every nonzero c, c is represented by Q if and only if cQ is isometric to Q. Let Q′ be a
quadratic form on another F-vector space W and e : Q ≃ Q′ an isometry. If Q is round, then Q′
is round.
-/
theorem map_isometryEquiv
    {W : Type w} [AddCommGroup W] [Module F W]
    {Q : QuadraticForm F V} {Q' : QuadraticForm F W}
    (hQ : Q.IsRound) (e : Q.IsometryEquiv Q') :
    Q'.IsRound := by
  intro d hd
  constructor
  · rintro ⟨x, hx⟩
    have hxQ : Q (e.symm x) = d := by
      rw [← e.map_app]
      simpa using hx
    have hsim : (d • Q).Equivalent Q :=
      (hQ d hd).mp ⟨e.symm x, hxQ⟩
    exact similarity_transport e d hsim
  · intro hsim'
    have hsim : (d • Q).Equivalent Q :=
      similarity_transport e.symm d hsim'
    obtain ⟨x, hx⟩ := (hQ d hd).mpr hsim
    refine ⟨e x, ?_⟩
    rw [e.map_app, hx]

/-- **Adjoining a binary factor preserves roundness.**

Let F be a field, V an F-vector space, and Q : V → F a quadratic form. Roundness means that,
for every nonzero c, c is represented by Q if and only if cQ is isometric to Q. If Q is round
and c ∈ F is nonzero, then Q ⊕ (−cQ), the form (x,y) ↦ Q(x) − cQ(y), is round.
-/
theorem prod_neg_smul
    {Q : QuadraticForm F V} (hQ : Q.IsRound)
    (c : F) (hc : c ≠ 0) :
    (Q.prod ((-c) • Q)).IsRound := by
  let P := Q.prod ((-c) • Q)
  have hOne : ∃ e : V, Q e = 1 :=
    (hQ 1 one_ne_zero).mpr (by
      simpa only [one_smul] using Equivalent.refl Q)
  intro d hd
  constructor
  · rintro ⟨⟨x, y⟩, hxy⟩
    change Q x + -c * Q y = d at hxy
    by_cases hx : Q x = 0
    · have hy : Q y ≠ 0 := by
        intro hy
        apply hd
        rw [← hxy, hx, hy]
        ring
      have hyQ : ((Q y) • Q).Equivalent Q :=
        (hQ (Q y) hy).mp ⟨y, rfl⟩
      have hyP : ((Q y) • P).Equivalent P :=
        similarity_prod_of_similarity Q c (Q y) hyQ
      have hnegc : ((-c) • P).Equivalent P := by
        have hdet : 0 * 0 - c * (1 * 1) ≠ 0 := by
          simpa using neg_ne_zero.mpr hc
        refine ⟨?_⟩
        simpa only [P, zero_mul, one_mul, mul_one, zero_sub] using
          binaryMulIsometryEquiv Q c 0 1 hdet
      have hprod := similarity_mul P (-c) (Q y) hnegc hyP
      have hdc : d = (-c) * Q y := by
        rw [← hxy, hx]
        ring
      simpa [hdc] using hprod
    · by_cases hy : Q y = 0
      · have hxQ : ((Q x) • Q).Equivalent Q :=
          (hQ (Q x) hx).mp ⟨x, rfl⟩
        have hxP : ((Q x) • P).Equivalent P :=
          similarity_prod_of_similarity Q c (Q x) hxQ
        have hdx : d = Q x := by
          rw [← hxy, hy]
          ring
        simpa [hdx] using hxP
      · let t : F := c * (Q y / Q x)
        have hratioQ : ((Q y / Q x) • Q).Equivalent Q :=
          hQ.ratio_equivalent Q hy hx
        obtain ⟨eratio⟩ := hratioQ
        let eSecond : ((-t) • Q).IsometryEquiv ((-c) • Q) := by
          have hsource : (-t) • Q = (-c) • ((Q y / Q x) • Q) := by
            ext z
            simp only [t, smul_apply]
            ring
          exact (IsometryEquiv.ofEq hsource).trans (eratio.smul (-c))
        let eProd : (Q.prod ((-t) • Q)).IsometryEquiv P :=
          (IsometryEquiv.refl Q).prod eSecond
        have hdt : 1 - t ≠ 0 := by
          intro hzero
          have ht : t = 1 := (sub_eq_zero.mp hzero).symm
          dsimp only [t] at ht
          field_simp [hx] at ht
          apply hd
          rw [← hxy, ← ht]
          ring
        have hbin : ((1 - t) • (Q.prod ((-t) • Q))).Equivalent
            (Q.prod ((-t) • Q)) := by
          have hdet : 1 * 1 - t * (1 * 1) ≠ 0 := by
            simpa using hdt
          refine ⟨?_⟩
          simpa only [one_mul, mul_one] using
            binaryMulIsometryEquiv Q t 1 1 hdet
        have hfactor : ((1 - t) • P).Equivalent P :=
          similarity_transport eProd (1 - t) hbin
        have hxQ : ((Q x) • Q).Equivalent Q :=
          (hQ (Q x) hx).mp ⟨x, rfl⟩
        have hxP : ((Q x) • P).Equivalent P :=
          similarity_prod_of_similarity Q c (Q x) hxQ
        have hprod := similarity_mul P (Q x) (1 - t) hxP hfactor
        have hdprod : d = Q x * (1 - t) := by
          rw [← hxy]
          dsimp only [t]
          field_simp [hx]
          ring
        simpa [hdprod] using hprod
  · intro hsim
    obtain ⟨e⟩ := hsim
    obtain ⟨one, hone⟩ := hOne
    refine ⟨e (one, 0), ?_⟩
    rw [e.map_app]
    simp [smul_apply, smul_eq_mul, QuadraticMap.prod_apply, hone]

end QuadraticMap.IsRound

end
