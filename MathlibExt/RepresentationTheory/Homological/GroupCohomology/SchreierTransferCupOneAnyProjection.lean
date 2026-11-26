/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneAny
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.Homology
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryIndependence
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferCupProjection

/-!
# Cup projection with a degree-one factor in every degree

Let A and B be k-linear G-representations, let H ≤ G have finite index and let T be a right
transversal. For x : G → A and y : Hᵠ → B, set Kᵠ(g) = ∑ₜ ρ_A(t⁻¹)x(t) ⊗
ρ_B(t⁻¹)y(T.schreierFactorTuple t g). The first coefficient is in A and the second in B.

If x is a one-cocycle and y is a q-cocycle, including q = 0, the uniform identity is
cor_Tᵠ⁺¹(x|H ∪ y) = x ∪ cor_Tᵠ(y) − dᵠKᵠ. It retains the inhomogeneous signs (−1)ʲ⁺¹ on the
contracted tuple terms and the identification 1+q = q+1.

Passing to cohomology gives cor_T(res(x) ∪ y) = x ∪ cor_T(y) in Hᵠ⁺¹(G,A ⊗ B), after the
canonical restriction–tensor coefficient comparison. The same identity holds for canonical
transversal-independent corestriction.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Finite representatives for the uniform cup projection formula.

The finite-index hypothesis gives a finite enumeration of T for the degree-q tensor-valued
comparison sum. -/
noncomputable local instance cupOneAnyProjectionTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Equal positive-degree classes from a subtracted boundary.

If two included degree-(q+1) cycle cochains satisfy z₁ = z₂ − dᵠb, then their images under the
group-cohomology projection are equal. -/
theorem π_eq_of_iCocycles_eq_sub_boundary_succ
    (A : Rep k G) (q : ℕ) (z₁ z₂ : cocycles A (q + 1))
    (b : (inhomogeneousCochains A).X q)
    (h : (iCocycles A (q + 1)).hom z₁ =
      (iCocycles A (q + 1)).hom z₂ -
        ((inhomogeneousCochains A).d q (q + 1)).hom b) :
    π A (q + 1) z₁ = π A (q + 1) z₂ := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply π_eq_zero_of_boundary_succ A q (z₁ - z₂) (-b)
  rw [map_sub, map_neg, h]
  abel

/-- Transport a cycle across an equality of natural-number degrees. -/
private noncomputable def cyclesCast
    {C : CochainComplex (ModuleCat k) ℕ} {m n : ℕ}
    (h : m = n) (z : C.cycles m) : C.cycles n :=
  cast (congrArg (fun r ↦ ↥(C.cycles r)) h) z

/-- Inclusion of a degree-transported cycle. -/
private theorem iCycles_cyclesCast
    {C : CochainComplex (ModuleCat k) ℕ} {m n : ℕ}
    (h : m = n) (z : C.cycles m) :
    (C.iCycles n).hom (cyclesCast h z) =
      (C.XIsoOfEq h).hom.hom ((C.iCycles m).hom z) := by
  subst h
  rfl

/-- The elementary carrier cast agrees with the canonical cycle transport
isomorphism. -/
private theorem cyclesCast_eq_cyclesIsoOfEq
    {C : CochainComplex (ModuleCat k) ℕ} {m n : ℕ}
    (h : m = n) (z : C.cycles m) :
    cyclesCast h z = (C.cyclesIsoOfEq h).hom.hom z := by
  subst h
  rfl

/-- The cup cochain with a degree-one first factor.

For arbitrary x : G → A and y : Gᵠ → B, define (x ∪ y)(g₀,…,gᵠ) = x(g₀) ⊗ ρ_B(g₀)y(g₁,…,gᵠ). -/
noncomputable def cupCochainOneAny
    (A B : Rep k G) (q : ℕ) (x : G → A)
    (y : (Fin q → G) → B) :
    (Fin (q + 1) → G) → (A ⊗ B : Rep k G) :=
  fun g ↦ x (g 0) ⊗ₜ[k] B.ρ (g 0) (y (Fin.tail g))

/-- Values of the one-by-q cup cochain.

The cup cochain on a tuple g is x(g₀) ⊗ ρ_B(g₀)y(Fin.tail g). -/
@[simp]
theorem cupCochainOneAny_apply
    (A B : Rep k G) (q : ℕ) (x : G → A)
    (y : (Fin q → G) → B) (g : Fin (q + 1) → G) :
    cupCochainOneAny A B q x y g =
      x (g 0) ⊗ₜ[k] B.ρ (g 0) (y (Fin.tail g)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The graded cup pairing in one-by-q coordinates.

The degree-(1,q) component of the inhomogeneous cup pairing, applied to the tensor of the
unary cochain x and q-cochain y, gives cupCochainOneAny after reindexing the target tuple by
1+q = q+1. -/
theorem inhomogeneousCupPairing_one_any_apply
    (A B : Rep k G) (q : ℕ) (x : G → A)
    (y : (Fin q → G) → B) (g : Fin (q + 1) → G) :
    (((inhomogeneousCupPairing G k A B).pair 1 q).hom
      ((fun h : Fin 1 → G ↦ x (h 0)) ⊗ₜ[k] y))
        (fun i ↦ g (Fin.cast (Nat.one_add q) i)) =
        cupCochainOneAny A B q x y g := by
  rw [inhomogeneousCupPairing_apply, cupCochainOneAny_apply]
  congr 2
  · congr 1
    simp [Fin.partialProd]
  · congr 1
    funext i
    congr 1
    apply Fin.ext
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of degree transport on an inhomogeneous cochain. -/
private theorem inhomogeneousCochains_XIsoOfEq_apply
    (A : Rep k G) {m n : ℕ} (h : m = n)
    (c : (Fin m → G) → A) (g : Fin n → G) :
    ((inhomogeneousCochains A).XIsoOfEq h).hom.hom c g =
      c (fun i ↦ g (Fin.cast h i)) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The one-by-q cup pairing after degree transport.

Transporting the graded pairing result from degree 1+q to q+1 by the canonical complex
component isomorphism gives the cochain g ↦ x(g₀) ⊗ ρ_B(g₀)y(Fin.tail g). -/
theorem inhomogeneousCupPairing_one_any_cast_apply
    (A B : Rep k G) (q : ℕ) (x : G → A)
    (y : (Fin q → G) → B) (g : Fin (q + 1) → G) :
    (((inhomogeneousCochains (A ⊗ B)).XIsoOfEq
      (Nat.one_add q)).hom.hom
        (((inhomogeneousCupPairing G k A B).pair 1 q).hom
          ((fun h : Fin 1 → G ↦ x (h 0)) ⊗ₜ[k] y))) g =
      cupCochainOneAny A B q x y g := by
  rw [inhomogeneousCochains_XIsoOfEq_apply]
  exact inhomogeneousCupPairing_one_any_apply A B q x y g

/-- A summand of the uniform projection comparison cochain.

For a representative t and a q-tuple g, the summand is ρ_A(t⁻¹)x(t) ⊗
ρ_B(t⁻¹)y(T.schreierFactorTuple t g). -/
noncomputable def cupProjectionHomotopyOneAnyTerm
    (A B : Rep k G) (T : H.RightTransversal)
    (q : ℕ) (x : G → A) (y : (Fin q → H) → B)
    (t : (T : Set G)) (g : Fin q → G) : (A ⊗ B : Rep k G) :=
  A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
    B.ρ (t : G)⁻¹ (y (T.schreierFactorTuple t g))

/-- The degree-q projection comparison cochain.

Sum the inverse-weighted tensor summands over t ∈ T to define Kᵠ : Gᵠ → A ⊗ B for arbitrary
cochains x and y. -/
noncomputable def cupProjectionHomotopyOneAny
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (q : ℕ) (x : G → A) (y : (Fin q → H) → B) :
    (Fin q → G) → (A ⊗ B : Rep k G) :=
  fun g ↦ ∑ t : (T : Set G),
    cupProjectionHomotopyOneAnyTerm A B T q x y t g

/-- Values of the uniform projection comparison sum.

For g : Fin q → G, Kᵠ(g) is the sum over T of cupProjectionHomotopyOneAnyTerm A B T q x y t g. -/
@[simp]
theorem cupProjectionHomotopyOneAny_apply
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (q : ℕ) (x : G → A) (y : (Fin q → H) → B)
    (g : Fin q → G) :
    cupProjectionHomotopyOneAny A B T q x y g =
      ∑ t : (T : Set G),
        cupProjectionHomotopyOneAnyTerm A B T q x y t g :=
  rfl

private theorem tensor_rho_tmul_one_any
    (A B : Rep k G) (g : G) (a : A) (b : B) :
    (A ⊗ B : Rep k G).ρ g (a ⊗ₜ[k] b) =
      A.ρ g a ⊗ₜ[k] B.ρ g b := by
  change TensorProduct.map (A.ρ g) (B.ρ g) (a ⊗ₜ[k] b) = _
  rw [TensorProduct.map_tmul]

/-- The tensor action on the uniform projection cochain.

Applying g₀ to Kᵠ(g) and reindexing by u = r(t,g₀) gives terms ρ_A(g₀u⁻¹)x(u) ⊗
ρ_B(g₀u⁻¹)y(T.schreierFactorTuple u g). -/
theorem rho_cupProjectionHomotopyOneAny
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (q : ℕ) (x : G → A) (y : (Fin q → H) → B)
    (g₀ : G) (g : Fin q → G) :
    (A ⊗ B : Rep k G).ρ g₀
        (cupProjectionHomotopyOneAny A B T q x y g) =
      ∑ t : (T : Set G),
        A.ρ (g₀ * (T.schreierRep t g₀ : G)⁻¹)
            (x (T.schreierRep t g₀ : G)) ⊗ₜ[k]
          B.ρ (g₀ * (T.schreierRep t g₀ : G)⁻¹)
            (y (T.schreierFactorTuple
              (T.schreierRep t g₀) g)) := by
  rw [cupProjectionHomotopyOneAny_apply, map_sum]
  calc
    _ = ∑ t : (T : Set G),
        A.ρ (g₀ * (t : G)⁻¹) (x (t : G)) ⊗ₜ[k]
          B.ρ (g₀ * (t : G)⁻¹)
            (y (T.schreierFactorTuple t g)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [cupProjectionHomotopyOneAnyTerm,
        tensor_rho_tmul_one_any]
      congr 1
      · rw [← Module.End.mul_apply, ← map_mul]
      · rw [← Module.End.mul_apply, ← map_mul]
    _ = _ :=
      (T.schreierRepEquiv g₀).sum_comp
        (fun t : (T : Set G) ↦
          A.ρ (g₀ * (t : G)⁻¹) (x (t : G)) ⊗ₜ[k]
            B.ρ (g₀ * (t : G)⁻¹)
              (y (T.schreierFactorTuple t g))) |>.symm

/-- The one-by-q cup with a transferred cochain.

The cup x ∪ cor_Tᵠ(y) on g is the sum of x(g₀) ⊗ ρ_B(g₀r(t,g₀)⁻¹)y on the factor tuple of the
tail starting at r(t,g₀). -/
theorem cupCochainOneAny_corestrictionCochain
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (q : ℕ) (x : G → A) (y : (Fin q → H) → B)
    (g : Fin (q + 1) → G) :
    cupCochainOneAny A B q x (corestrictionCochain B T q y) g =
      ∑ t : (T : Set G),
        x (g 0) ⊗ₜ[k]
          B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
            (y (T.schreierFactorTuple
              (T.schreierRep t (g 0)) (Fin.tail g))) := by
  rw [cupCochainOneAny_apply, corestrictionCochain_apply,
    map_sum, TensorProduct.tmul_sum]
  calc
    _ = ∑ t : (T : Set G),
        x (g 0) ⊗ₜ[k]
          B.ρ (g 0 * (t : G)⁻¹)
            (y (T.schreierFactorTuple t (Fin.tail g))) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [← Module.End.mul_apply, ← map_mul]
    _ = _ :=
      (T.schreierRepEquiv (g 0)).sum_comp
        (fun t : (T : Set G) ↦
          x (g 0) ⊗ₜ[k]
            B.ρ (g 0 * (t : G)⁻¹)
              (y (T.schreierFactorTuple t (Fin.tail g)))) |>.symm

/-- The signed contraction sum of a subgroup cocycle.

If dᵠy = 0, summing the inverse-weighted y-values on contracted factor tuples with
coefficients (−1)ʲ⁺¹ equals the negative leading term ρ_B(g₀r(t,g₀)⁻¹)y on the tail scan. -/
theorem sum_smul_rho_inv_factorTuple_contract_of_cocycle
    (B : Rep k G) (T : H.RightTransversal)
    (q : ℕ) (y : (Fin q → H) → B)
    (hy : (inhomogeneousCochains.d (Rep.res H.subtype B) q).hom y = 0)
    (t : (T : Set G)) (g : Fin (q + 1) → G) :
    (∑ j : Fin (q + 1), (-1 : k) ^ ((j : ℕ) + 1) •
      B.ρ (t : G)⁻¹
        (y (T.schreierFactorTuple t
          (Fin.contractNth j (fun a b : G ↦ a * b) g)))) =
      -B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
        (y (T.schreierFactorTuple
          (T.schreierRep t (g 0)) (Fin.tail g))) := by
  let htuple := T.schreierFactorTuple t g
  have hyPoint := congrFun hy htuple
  simp only [inhomogeneousCochains.d_hom_apply] at hyPoint
  change (Rep.res H.subtype B).ρ (htuple 0)
      (y (fun i ↦ htuple i.succ)) +
        ∑ j : Fin (q + 1), (-1 : k) ^ ((j : ℕ) + 1) •
          y (Fin.contractNth j (fun a b : H ↦ a * b) htuple) = 0
    at hyPoint
  have htail : (fun i : Fin q ↦ htuple i.succ) = Fin.tail htuple := by
    rw [Fin.tail_def]
  rw [htail] at hyPoint
  have hsum :
      (∑ j : Fin (q + 1), (-1 : k) ^ ((j : ℕ) + 1) •
        y (Fin.contractNth j (fun a b : H ↦ a * b) htuple)) =
      -(Rep.res H.subtype B).ρ (htuple 0)
        (y (Fin.tail htuple)) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa only [add_comm] using hyPoint
  calc
    (∑ j : Fin (q + 1), (-1 : k) ^ ((j : ℕ) + 1) •
        B.ρ (t : G)⁻¹
          (y (T.schreierFactorTuple t
            (Fin.contractNth j (fun a b : G ↦ a * b) g)))) =
      B.ρ (t : G)⁻¹
        (∑ j : Fin (q + 1), (-1 : k) ^ ((j : ℕ) + 1) •
          y (Fin.contractNth j (fun a b : H ↦ a * b) htuple)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
        congr 1
        rw [Subgroup.RightTransversal.schreierFactorTuple_contractNth]
    _ = B.ρ (t : G)⁻¹
        (-(Rep.res H.subtype B).ρ (htuple 0)
          (y (Fin.tail htuple))) := by rw [hsum]
    _ = -B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
        (y (T.schreierFactorTuple
          (T.schreierRep t (g 0)) (Fin.tail g))) := by
      rw [map_neg]
      congr 1
      dsimp only [htuple]
      rw [Subgroup.RightTransversal.schreierFactorTuple_zero]
      change B.ρ (t : G)⁻¹
          (B.ρ (T.schreierFactor t (g 0) : G)
            (y (Fin.tail (T.schreierFactorTuple t g)))) = _
      rw [← Module.End.mul_apply, ← map_mul,
        T.inv_mul_schreierFactor t (g 0)]
      congr 2
      exact (T.schreierFactorTuple_tail t g).symm

/-- The signed contraction sum of the projection cochain.

For an H-q-cocycle y, ∑ⱼ(−1)ʲ⁺¹Kᵠ(contractⱼ g) is minus the sum of ρ_A(t⁻¹)x(t) ⊗
ρ_B(g₀r(t,g₀)⁻¹)y on the tail scan. -/
theorem sum_smul_cupProjectionHomotopyOneAny_contract_of_cocycle
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (q : ℕ) (x : G → A) (y : (Fin q → H) → B)
    (hy : (inhomogeneousCochains.d (Rep.res H.subtype B) q).hom y = 0)
    (g : Fin (q + 1) → G) :
    (∑ j : Fin (q + 1), (-1 : k) ^ ((j : ℕ) + 1) •
      cupProjectionHomotopyOneAny A B T q x y
        (Fin.contractNth j (fun a b : G ↦ a * b) g)) =
      -∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
            (y (T.schreierFactorTuple
              (T.schreierRep t (g 0)) (Fin.tail g))) := by
  simp_rw [cupProjectionHomotopyOneAny_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ t : (T : Set G), ∑ j : Fin (q + 1),
        (-1 : k) ^ ((j : ℕ) + 1) •
          cupProjectionHomotopyOneAnyTerm A B T q x y t
            (Fin.contractNth j (fun a b : G ↦ a * b) g)) =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          (∑ j : Fin (q + 1), (-1 : k) ^ ((j : ℕ) + 1) •
            B.ρ (t : G)⁻¹
              (y (T.schreierFactorTuple t
                (Fin.contractNth j (fun a b : G ↦ a * b) g)))) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro j _
        unfold cupProjectionHomotopyOneAnyTerm
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    _ = ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          (-B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
            (y (T.schreierFactorTuple
              (T.schreierRep t (g 0)) (Fin.tail g)))) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [sum_smul_rho_inv_factorTuple_contract_of_cocycle
          B T q y hy t g]
    _ = -∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
            (y (T.schreierFactorTuple
              (T.schreierRep t (g 0)) (Fin.tail g))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t _
        rw [TensorProduct.tmul_neg]

/-- The transferred one-by-q cup summand.

For a G-one-cocycle x, the inverse-weighted restricted cup term expands as the target x(g₀)
term plus the comparison term from ρ_A(t⁻¹)x(t) minus the translated comparison term from
ρ_A(g₀r(t,g₀)⁻¹)x(r(t,g₀)). The B-factor is the same translated tail-scan value in all three
terms. -/
theorem corestrictionCupOneAny_term
    (A B : Rep k G) (T : H.RightTransversal)
    (q : ℕ) (x : cocycles₁ A) (y : (Fin q → H) → B)
    (t : (T : Set G)) (g : Fin (q + 1) → G) :
    (A ⊗ B : Rep k G).ρ (t : G)⁻¹
        (cupCochainOneAny
          (Rep.res H.subtype A) (Rep.res H.subtype B) q
          (fun h : H ↦ x (h : G)) y
          (T.schreierFactorTuple t g)) =
      x (g 0) ⊗ₜ[k]
          B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
            (y (T.schreierFactorTuple
              (T.schreierRep t (g 0)) (Fin.tail g))) +
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
            (y (T.schreierFactorTuple
              (T.schreierRep t (g 0)) (Fin.tail g))) -
        A.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
            (x (T.schreierRep t (g 0) : G)) ⊗ₜ[k]
          B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
            (y (T.schreierFactorTuple
              (T.schreierRep t (g 0)) (Fin.tail g))) := by
  rw [cupCochainOneAny_apply, tensor_rho_tmul_one_any]
  rw [Subgroup.RightTransversal.schreierFactorTuple_zero]
  have htail := T.schreierFactorTuple_tail t g
  have hB :
      B.ρ (t : G)⁻¹
          (B.ρ (T.schreierFactor t (g 0) : G)
            (y (Fin.tail (T.schreierFactorTuple t g)))) =
        B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
          (y (T.schreierFactorTuple
            (T.schreierRep t (g 0)) (Fin.tail g))) := by
    rw [← Module.End.mul_apply, ← map_mul,
      T.inv_mul_schreierFactor t (g 0)]
    congr 2
    exact htail.symm
  change A.ρ (t : G)⁻¹
      (x (T.schreierFactor t (g 0) : G)) ⊗ₜ[k]
        B.ρ (t : G)⁻¹
          (B.ρ (T.schreierFactor t (g 0) : G)
            (y (Fin.tail (T.schreierFactorTuple t g)))) = _
  rw [hB, rho_inv_schreierFactor_cocycle A T x t (g 0),
    TensorProduct.sub_tmul, TensorProduct.add_tmul]

/-- The uniform cochain cup projection identity with its boundary.

For a G-one-cocycle x and an H-q-cocycle y, cor_Tᵠ⁺¹(x|H ∪ y) = x ∪ cor_Tᵠ(y) −
dᵠ(cupProjectionHomotopyOneAny A B T q x y), for every q ≥ 0. -/
theorem corestrictionCochain_cup_one_any
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (q : ℕ) (x : cocycles₁ A) (y : (Fin q → H) → B)
    (hy : (inhomogeneousCochains.d (Rep.res H.subtype B) q).hom y = 0) :
    corestrictionCochain (A ⊗ B) T (q + 1)
        (cupCochainOneAny
          (Rep.res H.subtype A) (Rep.res H.subtype B) q
          (fun h : H ↦ x (h : G)) y) =
      cupCochainOneAny A B q x (corestrictionCochain B T q y) -
        (inhomogeneousCochains.d (A ⊗ B) q).hom
          (cupProjectionHomotopyOneAny A B T q x y) := by
  funext g
  rw [corestrictionCochain_apply]
  have hterms :
      (∑ t : (T : Set G),
        (A ⊗ B : Rep k G).ρ (t : G)⁻¹
          (cupCochainOneAny
            (Rep.res H.subtype A) (Rep.res H.subtype B) q
            (fun h : H ↦ x (h : G)) y
            (T.schreierFactorTuple t g))) =
        ∑ t : (T : Set G),
          (x (g 0) ⊗ₜ[k]
              B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
                (y (T.schreierFactorTuple
                  (T.schreierRep t (g 0)) (Fin.tail g))) +
            A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
              B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
                (y (T.schreierFactorTuple
                  (T.schreierRep t (g 0)) (Fin.tail g))) -
            A.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
                (x (T.schreierRep t (g 0) : G)) ⊗ₜ[k]
              B.ρ (g 0 * (T.schreierRep t (g 0) : G)⁻¹)
                (y (T.schreierFactorTuple
                  (T.schreierRep t (g 0)) (Fin.tail g)))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCupOneAny_term A B T q x y t g
  rw [hterms, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← cupCochainOneAny_corestrictionCochain A B T q x y g]
  have hrho := rho_cupProjectionHomotopyOneAny
    A B T q x y (g 0) (Fin.tail g)
  have hinternal :=
    sum_smul_cupProjectionHomotopyOneAny_contract_of_cocycle
      A B T q x y hy g
  simp only [Pi.sub_apply, inhomogeneousCochains.d_hom_apply]
  have htail : (fun i : Fin q ↦ g i.succ) = Fin.tail g := by
    rw [Fin.tail_def]
  rw [htail]
  rw [hrho, hinternal]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- Cycle-representative form of the arbitrary `(1,q)` projection formula. -/
private theorem corestriction_cupCycles_one_any
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (q : ℕ) (x : cocycles₁ A)
    (y : cocycles (Rep.res H.subtype B) q) :
    let xA := (isoCocycles₁ A).inv x
    let xH := HomologicalComplex.cyclesMap
      (cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))) 1 xA
    let cupH₀ := ((inhomogeneousCupPairing H k
      (Rep.res H.subtype A) (Rep.res H.subtype B)).pairCycles 1 q).hom
        (xH ⊗ₜ[k] y)
    let cupH := cyclesCast (Nat.one_add q) cupH₀
    let cupHT := HomologicalComplex.cyclesMap
      (cochainsMap (MonoidHom.id H)
        (Rep.resTensorIso H.subtype A B).hom) (q + 1) cupH
    let lhs := HomologicalComplex.cyclesMap
      (corestrictionCochains (A ⊗ B) T) (q + 1) cupHT
    let yG := HomologicalComplex.cyclesMap
      (corestrictionCochains B T) q y
    let rhs₀ := ((inhomogeneousCupPairing G k A B).pairCycles 1 q).hom
      (xA ⊗ₜ[k] yG)
    let rhs := cyclesCast (Nat.one_add q) rhs₀
    π (A ⊗ B) (q + 1) lhs = π (A ⊗ B) (q + 1) rhs := by
  dsimp only
  apply π_eq_of_iCocycles_eq_sub_boundary_succ
    (A ⊗ B) q _ _
    (cupProjectionHomotopyOneAny A B T q x
      (iCocycles (Rep.res H.subtype B) q y))
  apply inhomogeneousCochains.ext
  intro g
  have hxA := isoCocycles₁_inv_comp_iCocycles_apply A x
  have hxRawA :
      (iCocycles A 1).hom ((isoCocycles₁ A).inv x) =
        (fun h : Fin 1 → G ↦ x (h 0)) := by
    rw [hxA]
    rfl
  have hxRestrict :
      ((cochainsMap H.subtype
        (𝟙 (Rep.res H.subtype A))).f 1).hom
          (fun h : Fin 1 → G ↦ x (h 0)) =
        (fun h : Fin 1 → H ↦ x (h 0 : G)) := by
    rfl
  have hxH := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))) 1)
    ((isoCocycles₁ A).inv x)
  have hcupH :=
    HomologicalComplex.CochainGradedPairing.pairCycles_i_apply k
      (inhomogeneousCupPairing H k
        (Rep.res H.subtype A) (Rep.res H.subtype B))
      1 q
      (HomologicalComplex.cyclesMap
        (cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))) 1
        ((isoCocycles₁ A).inv x)) y
  have hcupHCast := iCycles_cyclesCast (k := k) (Nat.one_add q)
    (((inhomogeneousCupPairing H k
      (Rep.res H.subtype A) (Rep.res H.subtype B)).pairCycles 1 q).hom
        (HomologicalComplex.cyclesMap
            (cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))) 1
            ((isoCocycles₁ A).inv x) ⊗ₜ[k] y))
  have hcupHT := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (MonoidHom.id H)
        (Rep.resTensorIso H.subtype A B).hom) (q + 1))
    (cyclesCast (Nat.one_add q)
      (((inhomogeneousCupPairing H k
        (Rep.res H.subtype A) (Rep.res H.subtype B)).pairCycles 1 q).hom
          (HomologicalComplex.cyclesMap
              (cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))) 1
              ((isoCocycles₁ A).inv x) ⊗ₜ[k] y)))
  have hlhs := iCocycles_corestriction_cyclesMap
    (A ⊗ B) T (q + 1)
    (HomologicalComplex.cyclesMap
      (cochainsMap (MonoidHom.id H)
        (Rep.resTensorIso H.subtype A B).hom) (q + 1)
      (cyclesCast (Nat.one_add q)
        (((inhomogeneousCupPairing H k
          (Rep.res H.subtype A) (Rep.res H.subtype B)).pairCycles 1 q).hom
            (HomologicalComplex.cyclesMap
                (cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))) 1
                ((isoCocycles₁ A).inv x) ⊗ₜ[k] y))))
  have hyG := iCocycles_corestriction_cyclesMap B T q y
  have hrhs :=
    HomologicalComplex.CochainGradedPairing.pairCycles_i_apply k
      (inhomogeneousCupPairing G k A B) 1 q
      ((isoCocycles₁ A).inv x)
      (HomologicalComplex.cyclesMap (corestrictionCochains B T) q y)
  have hrhsCast := iCycles_cyclesCast (k := k) (Nat.one_add q)
    (((inhomogeneousCupPairing G k A B).pairCycles 1 q).hom
      ((isoCocycles₁ A).inv x ⊗ₜ[k]
        HomologicalComplex.cyclesMap (corestrictionCochains B T) q y))
  have hcoeff (f : (Fin (q + 1) → H) →
      (Rep.res H.subtype A ⊗ Rep.res H.subtype B : Rep k H)) :
      ((cochainsMap (MonoidHom.id H)
        (Rep.resTensorIso H.subtype A B).hom).f (q + 1)).hom f = f := by
    rfl
  have hcupExplicitH :
      ((inhomogeneousCochains
        (Rep.res H.subtype A ⊗ Rep.res H.subtype B)).XIsoOfEq
          (Nat.one_add q)).hom.hom
        (((inhomogeneousCupPairing H k
          (Rep.res H.subtype A) (Rep.res H.subtype B)).pair 1 q).hom
          ((fun h : Fin 1 → H ↦ x (h 0 : G)) ⊗ₜ[k]
            (iCocycles (Rep.res H.subtype B) q y))) =
        cupCochainOneAny (Rep.res H.subtype A)
          (Rep.res H.subtype B) q (fun h : H ↦ x (h : G))
          (iCocycles (Rep.res H.subtype B) q y) := by
    funext g
    exact inhomogeneousCupPairing_one_any_cast_apply
      (Rep.res H.subtype A) (Rep.res H.subtype B) q
      (fun h : H ↦ x (h : G))
      (iCocycles (Rep.res H.subtype B) q y) g
  have hcupExplicitG :
      ((inhomogeneousCochains (A ⊗ B)).XIsoOfEq
          (Nat.one_add q)).hom.hom
        (((inhomogeneousCupPairing G k A B).pair 1 q).hom
          ((fun h : Fin 1 → G ↦ x (h 0)) ⊗ₜ[k]
            (corestrictionCochain B T q
              (iCocycles (Rep.res H.subtype B) q y)))) =
        cupCochainOneAny A B q x
          (corestrictionCochain B T q
            (iCocycles (Rep.res H.subtype B) q y)) := by
    funext g
    exact inhomogeneousCupPairing_one_any_cast_apply A B q x
      (corestrictionCochain B T q
        (iCocycles (Rep.res H.subtype B) q y)) g
  simp only [ConcreteCategory.comp_apply] at hxA hxH hcupHT hlhs hyG
  -- All comparison maps above are identity-on-carriers; after exposing
  -- their cycle inclusions this is exactly the cochain formula.
  rw [hlhs, hcupHT, hcupHCast, hcupH, hxH, hxRawA,
    hxRestrict, hcoeff, hcupExplicitH, hrhsCast, hrhs, hxRawA, hyG,
    hcupExplicitG]
  rw [inhomogeneousCochains.d_def]
  exact congrFun
    (corestrictionCochain_cup_one_any A B T q x
      (iCocycles (Rep.res H.subtype B) q y)
      (by
        have hd := ConcreteCategory.congr_hom
          ((inhomogeneousCochains (Rep.res H.subtype B)).iCycles_d
            q (q + 1)) y
        simpa [ConcreteCategory.comp_apply,
          inhomogeneousCochains.d_def] using hd)) g

/-- The one-by-q projection formula for chosen-transversal classes.

For x ∈ H¹(G,A) and y ∈ Hᵠ(H,B|H), transfer of res(x) ∪ y equals x cupped with transfer of y
in Hᵠ⁺¹(G,A ⊗ B). The source uses the canonical restriction–tensor isomorphism and the target
degree identification. -/
theorem corestrictionOfRightTransversal_cup_one_any
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (q : ℕ) (x : H1 A)
    (y : groupCohomology (Rep.res H.subtype B) q) :
    corestrictionOfRightTransversal (A ⊗ B) T (q + 1)
        (groupCohomology.map (MonoidHom.id H)
          (Rep.resTensorIso H.subtype A B).hom (q + 1)
          (cupOneAny (Rep.res H.subtype A) (Rep.res H.subtype B) q
            (groupCohomology.map H.subtype
              (𝟙 (Rep.res H.subtype A)) 1 x ⊗ₜ[k] y))) =
      cupOneAny A B q
        (x ⊗ₜ[k] corestrictionOfRightTransversal B T q y) := by
  induction x using H1_induction_on with
  | h x =>
      induction y using groupCohomology_induction_on with
      | h y =>
          let xA := (isoCocycles₁ A).inv x
          let xH := HomologicalComplex.cyclesMap
            (cochainsMap H.subtype (𝟙 (Rep.res H.subtype A))) 1 xA
          let cupH₀ := ((inhomogeneousCupPairing H k
            (Rep.res H.subtype A)
            (Rep.res H.subtype B)).pairCycles 1 q).hom (xH ⊗ₜ[k] y)
          let cupH := cyclesCast (Nat.one_add q) cupH₀
          have hxmap := ConcreteCategory.congr_hom
            (groupCohomology.π_map H.subtype
              (𝟙 (Rep.res H.subtype A)) 1) xA
          simp only [ConcreteCategory.comp_apply] at hxmap
          simp only [H1π, ConcreteCategory.comp_apply]
          rw [hxmap]
          rw [cupOneAny_π_apply]
          have hcoeff := ConcreteCategory.congr_hom
            (groupCohomology.π_map (MonoidHom.id H)
              (Rep.resTensorIso H.subtype A B).hom (q + 1))
            (((inhomogeneousCochains
              (Rep.res H.subtype A ⊗ Rep.res H.subtype B)).cyclesIsoOfEq
                (Nat.one_add q)).hom.hom
              (((inhomogeneousCupPairing H k
                (Rep.res H.subtype A)
                (Rep.res H.subtype B)).pairCycles 1 q).hom
                (HomologicalComplex.cyclesMap
                    (cochainsMap H.subtype
                      (𝟙 (Rep.res H.subtype A))) 1 xA ⊗ₜ[k] y)))
          simp only [ConcreteCategory.comp_apply] at hcoeff
          rw [hcoeff]
          rw [corestrictionOfRightTransversal_π]
          rw [corestrictionOfRightTransversal_π]
          rw [cupOneAny_π_apply]
          simpa only [xA, xH, cupH₀, cupH,
            cyclesCast_eq_cyclesIsoOfEq] using
            (corestriction_cupCycles_one_any A B T q x y)

/-- The one-by-q projection formula for canonical corestriction.

Canonical corestriction satisfies cor_H^G(res(x) ∪ y) = x ∪ cor_H^G(y) for x ∈ H¹(G,A), y ∈
Hᵠ(H,B|H) and every q ≥ 0, with the stated tensor coefficient comparison. -/
theorem schreierCorestriction_cup_one_any
    (A B : Rep k G) [H.FiniteIndex] (q : ℕ) (x : H1 A)
    (y : groupCohomology (Rep.res H.subtype B) q) :
    schreierCorestriction H (A ⊗ B) (q + 1)
        (groupCohomology.map (MonoidHom.id H)
          (Rep.resTensorIso H.subtype A B).hom (q + 1)
          (cupOneAny (Rep.res H.subtype A) (Rep.res H.subtype B) q
            (groupCohomology.map H.subtype
              (𝟙 (Rep.res H.subtype A)) 1 x ⊗ₜ[k] y))) =
      cupOneAny A B q
        (x ⊗ₜ[k] schreierCorestriction H B q y) := by
  let T : H.RightTransversal := default
  rw [schreierCorestriction_eq_of_rightTransversal H (A ⊗ B) T (q + 1),
    schreierCorestriction_eq_of_rightTransversal H B T q]
  exact corestrictionOfRightTransversal_cup_one_any A B T q x y

end groupCohomology
