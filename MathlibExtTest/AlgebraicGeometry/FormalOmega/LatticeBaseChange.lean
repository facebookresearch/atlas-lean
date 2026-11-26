/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeBaseChange
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

open LT.LatticeTree

universe u

/-- Consumer with the original binders: the orbital ball of depth `0` is the fixed-vertex set. -/
private theorem exactSource {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (c : Kˣ) (γ : Matrix.GeneralLinearGroup (Fin 2) K) :
    orbitalBall (R := R) c 0 γ = fixedVertexSet γ :=
  orbitalBall_zero c γ

/-- Higher-universe consumer: vertices within depth `0` coincide, and depth is symmetric. -/
example {R : Type (u + 1)} [CommRing R] {K : Type (u + 1)} [Field K] [Algebra R K] (c : Kˣ)
    (n : ℕ) (v w : Vertex R K) :
    (Vertex.IsWithin c 0 v w ↔ v = w) ∧ (Vertex.IsWithin c n v w ↔ Vertex.IsWithin c n w v) :=
  ⟨Vertex.isWithin_zero_iff c v w, Vertex.isWithin_comm c n v w⟩

/-- Base change along the identity is the identity on vertices, and base change is
`GL₂`-equivariant. -/
example {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.baseChange (IntegralHom.refl R K) v = v ∧
      Vertex.baseChange (IntegralHom.refl R K) (Vertex.act g v) =
        Vertex.act ((IntegralHom.refl R K).mapGL g) (Vertex.baseChange (IntegralHom.refl R K) v) :=
  ⟨Vertex.baseChange_refl v, Vertex.baseChange_act _ g v⟩

/-- Boundary: for `c = 1` every vertex lies in every orbital ball of the identity. -/
example {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] (n : ℕ) :
    orbitalBall (R := R) (1 : Kˣ) n 1 = Set.univ :=
  orbitalBall_one (fun L => by rw [scalarGL_one, latticeMap_one]) n

/-! The fraction-field hypothesis of `IsFullLattice.baseChange` is needed: `ℤ × ℤ`, acting on
`ℚ(√2)` through its first factor, has the full lattice spanned by `(1, 0)`, `(√2, 0)`, `(0, 1)` and
`(0, √2)`, while its base change to `ℤ ⊆ ℝ` contains `(1, 0)` and `(√2, 0)`, which are independent
over `ℤ` but not over `ℝ`. -/

/-- The field `ℚ(√2)`, as an intermediate field of `ℝ`. -/
private noncomputable abbrev Q2 : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ {√2}

/-- `ℤ × ℤ` acting on `ℚ(√2)` through its first factor. -/
private noncomputable instance : Algebra (ℤ × ℤ) Q2 :=
  ((Int.castRingHom Q2).comp (RingHom.fst ℤ ℤ)).toAlgebra

/-- `√2` as an element of `ℚ(√2)`. -/
private noncomputable def sqrtTwo : Q2 :=
  ⟨√2, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

/-- The inclusion `ℚ(√2) → ℝ`, over the first projection `ℤ × ℤ → ℤ`. -/
private noncomputable def inclQ2 : IntegralHom (ℤ × ℤ) Q2 ℤ ℝ where
  toField := (IntermediateField.val Q2).toRingHom
  toBase := RingHom.fst ℤ ℤ
  commutes r := by simp [RingHom.algebraMap_toAlgebra]

/-- The `ℤ × ℤ`-span of `(1, 0)`, `(√2, 0)`, `(0, 1)` and `(0, √2)`. -/
private noncomputable def latticeQ2 : Submodule (ℤ × ℤ) (Fin 2 → Q2) :=
  Submodule.span (ℤ × ℤ) {![1, 0], ![sqrtTwo, 0], ![0, 1], ![0, sqrtTwo]}

/-- The zero divisor `(0, 1)` kills every vector. -/
private theorem smul_zero_one (v : Fin 2 → Q2) : ((0, 1) : ℤ × ℤ) • v = 0 := by
  funext i
  simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

/-- `latticeQ2` is a full lattice: no nonempty family is independent over `ℤ × ℤ`. -/
private theorem isFullLattice_latticeQ2 : Submodule.IsFullLattice Q2 latticeQ2 where
  fg := Submodule.fg_span (Set.toFinite _)
  linearIndepOn s _ hs := by
    have hempty : s = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun v hv => ?_
      have h := (linearIndependent_iff'.mp hs) {⟨v, hv⟩} (fun _ => ((0, 1) : ℤ × ℤ))
        (by simp [smul_zero_one]) ⟨v, hv⟩ (Finset.mem_singleton_self _)
      exact absurd (congrArg Prod.snd h) (by norm_num)
    subst hempty
    exact linearIndepOn_empty Q2 id
  span_eq_top := by
    rw [eq_top_iff]
    intro v _
    have hmem : ∀ x ∈ ({![1, 0], ![sqrtTwo, 0], ![0, 1], ![0, sqrtTwo]} : Set (Fin 2 → Q2)),
        x ∈ Submodule.span Q2 (latticeQ2 : Set (Fin 2 → Q2)) := fun x hx =>
      Submodule.subset_span (Submodule.subset_span hx)
    have hv : v = v 0 • ![(1 : Q2), 0] + v 1 • ![(0 : Q2), 1] := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem _ (by simp)))
      (Submodule.smul_mem _ _ (hmem _ (by simp)))

/-- Boundary: without `[IsFractionRing R K]`, the base change of a full lattice need not be a full
lattice. -/
example :
    ¬ ∀ (R' K' R K : Type) [CommRing R'] [Field K'] [Algebra R' K'] [CommRing R] [Field K]
      [Algebra R K] (ι : IntegralHom R' K' R K) (L' : Submodule R' (Fin 2 → K')),
      Submodule.IsFullLattice K' L' → Submodule.IsFullLattice K (latticeBaseChange ι L') := by
  intro h
  have hbc := h (ℤ × ℤ) Q2 ℤ ℝ inclQ2 latticeQ2 isFullLattice_latticeQ2
  set a : Fin 2 → ℝ := ![1, 0]
  set b : Fin 2 → ℝ := ![√2, 0]
  have ha : a ∈ latticeBaseChange inclQ2 latticeQ2 := by
    have e : vecMap inclQ2 ![(1 : Q2), 0] = a := by funext i; fin_cases i <;> simp [a, inclQ2]
    exact e ▸ vecMap_mem_latticeBaseChange inclQ2 (L' := latticeQ2)
      (Submodule.subset_span (by simp))
  have hb : b ∈ latticeBaseChange inclQ2 latticeQ2 := by
    have e : vecMap inclQ2 ![sqrtTwo, 0] = b := by
      funext i; fin_cases i <;> simp [b, inclQ2, sqrtTwo]
    exact e ▸ vecMap_mem_latticeBaseChange inclQ2 (L' := latticeQ2)
      (Submodule.subset_span (by simp))
  have hab : a ≠ b := by
    intro e
    have h0 := congrFun e 0
    simp only [a, b, Matrix.cons_val_zero] at h0
    exact irrational_sqrt_two.ne_one h0.symm
  have hZ : LinearIndepOn ℤ id {a, b} := by
    refine (LinearIndepOn.pair_iff id hab).mpr fun c d hcd => ?_
    have h0 : (c : ℝ) + d * √2 = 0 := by simpa [a, b] using congrFun hcd 0
    have hd : d = 0 := by
      by_contra hd
      exact ((irrational_sqrt_two.intCast_mul hd).intCast_add c).ne_zero h0
    subst hd
    exact ⟨by simpa using h0, rfl⟩
  have hR := Submodule.IsLattice.linearIndepOn (A := ℝ) {a, b}
    (Set.insert_subset ha (Set.singleton_subset_iff.mpr hb)) hZ
  have ha0 : a ≠ 0 := fun e => by simpa [a] using congrFun e 0
  refine (linearIndepOn_pair_iff id hab ha0).mp hR √2 ?_
  funext i; fin_cases i <;> simp [a, b]
