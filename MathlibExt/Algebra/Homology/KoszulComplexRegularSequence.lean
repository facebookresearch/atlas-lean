/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.KoszulComplexProductOne
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Data.List.OfFn

/-!
# Positive-degree exactness of weakly regular Koszul complexes

Induction on a finite ordered family uses the exterior-power splitting after
adjoining a coefficient. Weak regularity makes the new coefficient injective
on the previous generated-ideal quotient. This proves that every
positive-degree cycle is a boundary and that positive homology vanishes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace KoszulComplex

universe u v

section ProductStep

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

private theorem productOne_exact_cycles
    (y : M →ₗ[R] R) (f : R)
    (hy : ∀ n : ℕ, ∀ z : ⋀[R]^(n + 1) M,
      differential R M y n z = 0 →
        ∃ w : ⋀[R]^(n + 2) M, differential R M y (n + 1) w = z)
    (hf : IsSMulRegular (R ⧸ ideal R M y) f)
    (n : ℕ) (z : ⋀[R]^(n + 1) (M × R))
    (hz : differential R (M × R) (productOneFunctional R M y f) n z = 0) :
    ∃ w : ⋀[R]^(n + 2) (M × R),
      differential R (M × R) (productOneFunctional R M y f) (n + 1) w = z := by
  cases n with
  | zero =>
      let a : ⋀[R]^1 M := (exteriorPower.productOneDecompose R M 0 z).1
      let b : ⋀[R]^0 M := (exteriorPower.productOneDecompose R M 0 z).2
      have hsplit : exteriorPower.productOneAssemble R M 0 (a, b) = z :=
        exteriorPower.productOneAssemble_decompose R M 0 z
      let α := exteriorPower.zeroEquiv R M (differential R M y 0 a)
      let β := exteriorPower.zeroEquiv R M b
      have hscalar : α + f * β = 0 := by
        rw [← productOneDifferential_assemble_zero R M y f a b, hsplit, hz, map_zero]
      have hα : α ∈ ideal R M y := by
        refine ⟨exteriorPower.oneEquiv R M a, ?_⟩
        exact (congrArg (fun q => q a) (differential_zero_equiv R M y)).symm
      have hβ : β ∈ ideal R M y := by
        have hmul : f • Ideal.Quotient.mk (ideal R M y) β = 0 := by
          change Ideal.Quotient.mk (ideal R M y) (f * β) = 0
          have h := congrArg (Ideal.Quotient.mk (ideal R M y)) hscalar
          have ha0 : Ideal.Quotient.mk (ideal R M y) α = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr hα
          simpa only [map_add, ha0, map_zero, zero_add] using h
        exact Ideal.Quotient.eq_zero_iff_mem.mp (hf.right_eq_zero_of_smul hmul)
      obtain ⟨m, hm⟩ := hβ
      let w₁ := (exteriorPower.oneEquiv R M).symm m
      have hw₁ : differential R M y 0 w₁ = b := by
        apply (exteriorPower.zeroEquiv R M).injective
        rw [show exteriorPower.zeroEquiv R M (differential R M y 0 w₁) =
            y (exteriorPower.oneEquiv R M w₁) from
          congrArg (fun q => q w₁) (differential_zero_equiv R M y)]
        simpa only [w₁, LinearEquiv.apply_symm_apply] using hm
      have hadj : differential R M y 0 (a + f • w₁) = 0 := by
        apply (exteriorPower.zeroEquiv R M).injective
        simp only [map_add, map_smul, hw₁, map_zero]
        exact hscalar
      obtain ⟨w₀, hw₀⟩ := hy 0 (a + f • w₁) hadj
      refine ⟨exteriorPower.productOneAssemble R M 1 (w₀, -w₁), ?_⟩
      rw [productOneDifferential_assemble, hw₀, map_neg, hw₁, neg_neg]
      simp only [smul_neg, add_neg_cancel_right]
      exact hsplit
  | succ n =>
      let a : ⋀[R]^(n + 2) M := (exteriorPower.productOneDecompose R M (n + 1) z).1
      let b : ⋀[R]^(n + 1) M := (exteriorPower.productOneDecompose R M (n + 1) z).2
      have hsplit : exteriorPower.productOneAssemble R M (n + 1) (a, b) = z :=
        exteriorPower.productOneAssemble_decompose R M (n + 1) z
      have hmain : exteriorPower.productOneAssemble R M n
          (differential R M y (n + 1) a + f • b, -differential R M y n b) = 0 := by
        rw [← productOneDifferential_assemble R M y f n a b, hsplit]
        exact hz
      have hcoords := congrArg (exteriorPower.productOneDecompose R M n) hmain
      rw [exteriorPower.productOneDecompose_assemble, map_zero] at hcoords
      have hleft : differential R M y (n + 1) a + f • b = 0 :=
        congrArg Prod.fst hcoords
      have hright : differential R M y n b = 0 := by
        have h := congrArg Prod.snd hcoords
        exact neg_eq_zero.mp h
      obtain ⟨w₁, hw₁⟩ := hy n b hright
      have hadj : differential R M y (n + 1) (a + f • w₁) = 0 := by
        simpa only [map_add, map_smul, hw₁] using hleft
      obtain ⟨w₀, hw₀⟩ := hy (n + 1) (a + f • w₁) hadj
      refine ⟨exteriorPower.productOneAssemble R M (n + 2) (w₀, -w₁), ?_⟩
      rw [productOneDifferential_assemble, hw₀, map_neg, hw₁, neg_neg]
      simp only [smul_neg, add_neg_cancel_right]
      exact hsplit

end ProductStep

variable (R : Type u) [CommRing R]

/-- The actual coordinate equivalence between one extra free summand and
the standard finite free coefficient module. -/
def finiteFamilySnocModuleEquiv (n : ℕ) :
    ((Fin n → R) × R) ≃ₗ[R] (Fin (n + 1) → R) where
  toFun z := Fin.snoc z.1 z.2
  invFun z := (fun i => z i.castSucc, z (Fin.last n))
  left_inv z := by
    apply Prod.ext
    · funext i; simp
    · simp
  right_inv z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_add' z w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' r z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- The original finite-family functional is the literal product
functional under the actual last-coordinate equivalence. -/
theorem familyFunctional_comp_snocModuleEquiv
    {n : ℕ} (a : Fin (n + 1) → R) :
    (familyFunctional R a).comp (finiteFamilySnocModuleEquiv R n).toLinearMap =
      productOneFunctional R (Fin n → R)
        (familyFunctional R (fun i => a i.castSucc)) (a (Fin.last n)) := by
  apply LinearMap.ext
  rintro ⟨m, r⟩
  simp [finiteFamilySnocModuleEquiv, familyFunctional, Fintype.linearCombination_apply,
    Fin.sum_univ_castSucc, mul_comm]

/-- The actual family ideal is the ideal generated by its ordered list. -/
theorem finiteFamilyIdeal_eq_ofList {n : ℕ} (a : Fin n → R) :
    ideal R (Fin n → R) (familyFunctional R a) = Ideal.ofList (List.ofFn a) := by
  rw [familyIdeal_eq_span]
  apply congrArg Ideal.span
  ext r
  simp

/-- Every positive-degree cycle in the actual finite-family Koszul
complex is a boundary when its original ordered coefficient list is
weakly regular. The proof constructs the boundary by induction. -/
theorem finiteFamily_exact_cycles
    {n : ℕ} (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a))
    (k : ℕ) (z : ⋀[R]^(k + 1) (Fin n → R))
    (hz : differential R (Fin n → R) (familyFunctional R a) k z = 0) :
    ∃ w : ⋀[R]^(k + 2) (Fin n → R),
      differential R (Fin n → R) (familyFunctional R a) (k + 1) w = z := by
  induction n generalizing k with
  | zero =>
      have hX : CategoryTheory.Limits.IsZero ((familyComplex R a).X (k + 1)) :=
        familyComplex_isZero_above R a (k + 1) (by simp)
      let _ : Subsingleton (⋀[R]^(k + 1) (Fin 0 → R)) :=
        ModuleCat.isZero_iff_subsingleton.mp hX
      refine ⟨0, ?_⟩
      rw [map_zero]
      exact Subsingleton.elim _ _
  | succ n ih =>
      let a₀ : Fin n → R := fun i => a i.castSucc
      let f := a (Fin.last n)
      have ha' : RingTheory.Sequence.IsWeaklyRegular R ((List.ofFn a₀) ++ [f]) := by
        simpa only [List.ofFn_succ', List.concat_eq_append] using ha
      obtain ⟨ha₀, hf⟩ := (RingTheory.Sequence.isWeaklyRegular_append_iff R
        (List.ofFn a₀) [f]).mp ha'
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hf
      have hideal : (Ideal.ofList (List.ofFn a₀) • (⊤ : Submodule R R)) =
          ideal R (Fin n → R) (familyFunctional R a₀) := by
        rw [← finiteFamilyIdeal_eq_ofList R a₀, ← Ideal.one_eq_top, smul_eq_mul, mul_one]
      rw [hideal] at hf
      let e := finiteFamilySnocModuleEquiv R n
      have hforward : (familyFunctional R a).comp e.toLinearMap =
          productOneFunctional R (Fin n → R) (familyFunctional R a₀) f :=
        familyFunctional_comp_snocModuleEquiv R a
      have hId : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        intro m
        exact e.apply_symm_apply m
      have hback :
          (productOneFunctional R (Fin n → R) (familyFunctional R a₀) f).comp
            e.symm.toLinearMap = familyFunctional R a := by
        rw [← hforward, LinearMap.comp_assoc, hId, LinearMap.comp_id]
      let z' := exteriorPower.map (k + 1) e.symm.toLinearMap z
      have hz' : differential R ((Fin n → R) × R)
          (productOneFunctional R (Fin n → R) (familyFunctional R a₀) f) k z' = 0 := by
        calc
          _ = exteriorPower.map k e.symm.toLinearMap
              (differential R (Fin (n + 1) → R) (familyFunctional R a) k z) :=
            congrArg (fun q => q z)
              (differential_naturality R (Fin (n + 1) → R) (familyFunctional R a)
                (productOneFunctional R (Fin n → R) (familyFunctional R a₀) f)
                e.symm.toLinearMap hback k)
          _ = 0 := by rw [hz, map_zero]
      obtain ⟨w', hw'⟩ := productOne_exact_cycles R (Fin n → R)
        (familyFunctional R a₀) f (fun j x hx => ih a₀ ha₀ j x hx) hf k z' hz'
      refine ⟨exteriorPower.map (k + 2) e.toLinearMap w', ?_⟩
      calc
        _ = exteriorPower.map (k + 1) e.toLinearMap
            (differential R ((Fin n → R) × R)
              (productOneFunctional R (Fin n → R) (familyFunctional R a₀) f) (k + 1) w') :=
          congrArg (fun q => q w')
            (differential_naturality R ((Fin n → R) × R)
              (productOneFunctional R (Fin n → R) (familyFunctional R a₀) f)
              (familyFunctional R a) e.toLinearMap hforward (k + 1))
        _ = exteriorPower.map (k + 1) e.toLinearMap z' := by rw [hw']
        _ = z := by
          dsimp only [z']
          rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hId, exteriorPower.map_id]
          rfl

/-- Positive-degree cycle exactness for an original finite coefficient
type in its own universe. The enumerator is an actual equivalence of
index types; all exterior-power maps remain over the original ring. -/
theorem family_exact_cycles_of_isWeaklyRegular
    {I : Type v} [Fintype I] {n : ℕ} (a : I → R) (e : Fin n ≃ I)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun i => a (e i)))
    (k : ℕ) (z : ⋀[R]^(k + 1) (I → R))
    (hz : differential R (I → R) (familyFunctional R a) k z = 0) :
    ∃ w : ⋀[R]^(k + 2) (I → R),
      differential R (I → R) (familyFunctional R a) (k + 1) w = z := by
  let a₀ : Fin n → R := fun i => a (e i)
  let E : (Fin n → R) ≃ₗ[R] (I → R) :=
    LinearEquiv.piCongrLeft R (fun _ : I => R) e
  have hE (m : Fin n → R) (i : I) : E m i = m (e.symm i) := by
    change (Equiv.piCongrLeft (fun _ : I => R) e) m i = _
    simpa using (Equiv.piCongrLeft_apply (P := fun _ : I => R) (e := e) m i)
  have hforward : (familyFunctional R a).comp E.toLinearMap = familyFunctional R a₀ := by
    apply LinearMap.ext
    intro m
    simp only [LinearMap.comp_apply, familyFunctional, Fintype.linearCombination_apply]
    change (∑ i : I, E m i * a i) = ∑ j : Fin n, m j * a₀ j
    simp only [hE]
    change (∑ i : I, m (e.symm i) * a i) = ∑ j : Fin n, m j * a (e j)
    simpa only [e.symm_apply_apply] using
      (Equiv.sum_comp e (fun i => m (e.symm i) * a i)).symm
  have hId : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro m
    exact E.apply_symm_apply m
  have hback : (familyFunctional R a₀).comp E.symm.toLinearMap = familyFunctional R a := by
    rw [← hforward, LinearMap.comp_assoc, hId, LinearMap.comp_id]
  let z' := exteriorPower.map (k + 1) E.symm.toLinearMap z
  have hz' : differential R (Fin n → R) (familyFunctional R a₀) k z' = 0 := by
    calc
      _ = exteriorPower.map k E.symm.toLinearMap
          (differential R (I → R) (familyFunctional R a) k z) :=
        congrArg (fun q => q z) (differential_naturality R (I → R)
          (familyFunctional R a) (familyFunctional R a₀) E.symm.toLinearMap hback k)
      _ = 0 := by rw [hz, map_zero]
  obtain ⟨w', hw'⟩ := finiteFamily_exact_cycles R a₀ ha k z' hz'
  refine ⟨exteriorPower.map (k + 2) E.toLinearMap w', ?_⟩
  calc
    _ = exteriorPower.map (k + 1) E.toLinearMap
        (differential R (Fin n → R) (familyFunctional R a₀) (k + 1) w') :=
      congrArg (fun q => q w') (differential_naturality R (Fin n → R)
        (familyFunctional R a₀) (familyFunctional R a) E.toLinearMap hforward (k + 1))
    _ = exteriorPower.map (k + 1) E.toLinearMap z' := by rw [hw']
    _ = z := by
      dsimp only [z']
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hId, exteriorPower.map_id]
      rfl

/-- The original finite-family Koszul complex is exact in every
positive degree for a weakly regular coefficient sequence. -/
theorem familyComplex_exactAt_of_isWeaklyRegular
    {I : Type v} [Fintype I] {n : ℕ} (a : I → R) (e : Fin n ≃ I)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun i => a (e i))) (k : ℕ) :
    (familyComplex R a).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (K := familyComplex R a) (j := k + 1) (i := k + 2) (k := k)
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) by rfl))
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (k + 1) k by rfl)),
    CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro z hz
  change ((complex R (I → R) (familyFunctional R a)).d (k + 1) k) z = 0 at hz
  rw [complex_d_succ] at hz
  change differential R (I → R) (familyFunctional R a) k z = 0 at hz
  change ∃ w : ⋀[R]^(k + 2) (I → R),
    ((complex R (I → R) (familyFunctional R a)).d (k + 2) (k + 1)) w = z
  rw [complex_d_succ]
  exact family_exact_cycles_of_isWeaklyRegular R a e ha k z hz

/-- The Koszul complex of a finite weakly regular family has zero homology
in every positive degree. -/
theorem familyComplex_homology_isZero_of_isWeaklyRegular
    {I : Type v} [Fintype I] {n : ℕ} (a : I → R) (e : Fin n ≃ I)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun i => a (e i))) (k : ℕ) :
    CategoryTheory.Limits.IsZero ((familyComplex R a).homology (k + 1)) :=
  (familyComplex_exactAt_of_isWeaklyRegular R a e ha k).isZero_homology

end KoszulComplex
