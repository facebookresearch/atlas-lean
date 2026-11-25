/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DoubleComplex
import Mathlib.Tactic

/-!
# Tests for bounded double complexes

The fixtures are bounded double complexes over `ℤ` whose cells are `Fin d → ℤ` with
`d ∈ {0, 1}`:

* `point`: one copy of `ℤ` in bidegree `(0, 0)`;
* `square a b c d h`: copies of `ℤ` in bidegrees `{0, 1} × {0, 1}`, with horizontal maps
  `a` (row `0`) and `b` (row `1`) and vertical maps `c` (column `0`) and `d` (column `1`),
  commuting because `d * a = b * c`;
* `zeroComplex`: every cell is zero, with bound `N = 0`.

The signed total differential is evaluated on each kind of bidegree, including the
subtracted vertical term at `(1, 1)`. `point` keeps a nonzero class in total degree zero,
in its column cohomology, and on both `E₂` pages, so the column hypothesis of
`subsingleton_HTot_of_forall_subsingleton_colH` cannot be dropped. The identity square has
exact columns, so the theorem applies to a complex with nonzero total terms; the zero-map
square has a nonzero class in total degree one; the horizontal identity `square 1 1 0 0`
has a nonzero `colHdH` and a vanishing `E₂I` term at `(1, 0)`.
-/

universe u

namespace DoubleComplexBoundedTest

open DoubleComplex

private abbrev pointDim : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _, _ => 0

private abbrev point : Bounded ℤ where
  C p q := Fin (pointDim p q) → ℤ
  dH _ _ := 0
  dV _ _ := 0
  dH_sq _ _ := LinearMap.zero_comp _
  dV_sq _ _ := LinearMap.zero_comp _
  dHV_comm _ _ := rfl
  N := 1
  hBound p q h := by
    match p, q, h with
    | 0, 0, h => omega
    | 0, _ + 1, _ => exact inferInstanceAs (Subsingleton (Fin 0 → ℤ))
    | _ + 1, _, _ => exact inferInstanceAs (Subsingleton (Fin 0 → ℤ))

private abbrev squareDim : ℕ → ℕ → ℕ
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 => 1
  | _, _ => 0

private def squareH (a b : ℤ) :
    ∀ p q, (Fin (squareDim p q) → ℤ) →ₗ[ℤ] (Fin (squareDim (p + 1) q) → ℤ)
  | 0, 0 => a • LinearMap.id
  | 0, 1 => b • LinearMap.id
  | _, _ => 0

private def squareV (c d : ℤ) :
    ∀ p q, (Fin (squareDim p q) → ℤ) →ₗ[ℤ] (Fin (squareDim p (q + 1)) → ℤ)
  | 0, 0 => c • LinearMap.id
  | 1, 0 => d • LinearMap.id
  | _, _ => 0

private abbrev square (a b c d : ℤ) (h : d * a = b * c) : Bounded ℤ where
  C p q := Fin (squareDim p q) → ℤ
  dH := squareH a b
  dV := squareV c d
  dH_sq _ _ := LinearMap.zero_comp _
  dV_sq p q := by rcases p with _ | _ | p <;> exact LinearMap.zero_comp _
  dHV_comm p q := by
    refine LinearMap.ext fun x => funext fun i => ?_
    rcases p with _ | _ | p <;> rcases q with _ | _ | q
    · simp only [squareH, squareV, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Pi.smul_apply, smul_eq_mul]
      linear_combination x i * h
    all_goals simp [squareH, squareV]
  N := 2
  hBound p q hpq := by
    match p, q, hpq with
    | 0, 0, h | 0, 1, h | 1, 0, h | 1, 1, h => omega
    | 0, _ + 2, _ | 1, _ + 2, _ | _ + 2, _, _ =>
      exact inferInstanceAs (Subsingleton (Fin 0 → ℤ))

/-! Helpers. -/

private lemma vec_one_ne_zero {n : ℕ} [NeZero n] : (fun _ => 1 : Fin n → ℤ) ≠ 0 := fun h => by
  simpa using congrFun h 0

private lemma not_subsingleton_of_notMem {M : Type} [AddCommGroup M] [Module ℤ M]
    {p : Submodule ℤ M} {x : M} (hx : x ∉ p) : ¬ Subsingleton (M ⧸ p) := fun _ =>
  hx <| (Submodule.Quotient.mk_eq_zero p).1 (Subsingleton.elim _ _)

private lemma subsingleton_quot {M : Type} [AddCommGroup M] [Module ℤ M] [Subsingleton M]
    (p : Submodule ℤ M) : Subsingleton (M ⧸ p) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro x _
  rw [Subsingleton.elim x 0]
  exact p.zero_mem

/-! The signed total differential, evaluated on every kind of bidegree. -/

example (a b c d : ℤ) (h : d * a = b * c) (x : Tot (square a b c d h) 0) (i : Fin 1) :
    dTot (square a b c d h) 0 x ⟨(1, 0), rfl⟩ i = a * x ⟨(0, 0), rfl⟩ i := by
  rw [dTot_apply_succ_zero]
  rfl

example (a b c d : ℤ) (h : d * a = b * c) (x : Tot (square a b c d h) 0) (i : Fin 1) :
    dTot (square a b c d h) 0 x ⟨(0, 1), rfl⟩ i = c * x ⟨(0, 0), rfl⟩ i := by
  rw [dTot_apply_zero_succ]
  rfl

/-- The vertical part carries the sign `(-1) ^ p`: at `(1, 1)` it is subtracted. -/
example (a b c d : ℤ) (h : d * a = b * c) (x : Tot (square a b c d h) 1) (i : Fin 1) :
    dTot (square a b c d h) 1 x ⟨(1, 1), rfl⟩ i
      = b * x ⟨(0, 1), rfl⟩ i - d * x ⟨(1, 0), rfl⟩ i := by
  rw [dTot_apply_succ_succ]
  change b * x ⟨(0, 1), rfl⟩ i + (-1) ^ (0 + 1) * (d * x ⟨(1, 0), rfl⟩ i) = _
  ring

example (D : Bounded ℤ) (n : ℕ) (h : 0 + (n + 1) = n + 1) : dTotH D ⟨(0, n + 1), h⟩ = 0 := rfl

example (D : Bounded ℤ) (n : ℕ) (h : n + 1 + 0 = n + 1) : dTotV D ⟨(n + 1, 0), h⟩ = 0 := rfl

/-- Without the sign, `dTot 1 ∘ dTot 0` would be `2` on the identity square. -/
example (x : Tot (square 1 1 1 1 rfl) 0) (i : Fin 1) :
    dTot (square 1 1 1 1 rfl) 1 (dTot (square 1 1 1 1 rfl) 0 x) ⟨(1, 1), rfl⟩ i = 0 := by
  rw [dTot_apply_succ_succ, dTot_apply_zero_succ, dTot_apply_succ_zero]
  change 1 * (1 * x ⟨(0, 0), rfl⟩ i) + (-1) ^ (0 + 1) * (1 * (1 * x ⟨(0, 0), rfl⟩ i)) = 0
  ring

/-! `point`: one copy of `ℤ` in bidegree `(0, 0)`. -/

private instance (n : ℕ) : Subsingleton (Tot point (n + 1)) :=
  ⟨fun f g => funext fun i =>
    @Subsingleton.elim _ (point.hBound _ _ (by show 1 ≤ _ ∨ 1 ≤ _; have := i.2; omega)) _ _⟩

private noncomputable def pointGen : Tot point 0 := Pi.single ⟨(0, 0), rfl⟩ (fun _ => 1)

private lemma pointGen_mem : pointGen ∈ LinearMap.ker (dTot point 0) :=
  LinearMap.mem_ker.2 (Subsingleton.elim _ _)

/-- `HTotB D 0 = ⊥`, so the degree-zero cocycle `pointGen` has a nonzero class. -/
private lemma point_HTot_zero : ¬ Subsingleton (HTot point 0) := by
  refine not_subsingleton_of_notMem (x := (⟨pointGen, pointGen_mem⟩ : LinearMap.ker _)) ?_
  change _ ∉ (⊥ : Submodule ℤ _)
  rw [Submodule.mem_bot]
  intro h
  have := congrFun (congrFun (congrArg Subtype.val h) ⟨(0, 0), rfl⟩) 0
  simp only [pointGen, Pi.single_eq_same] at this
  simp at this

example : ¬ Subsingleton (HTot point 0) := point_HTot_zero

example (n : ℕ) : Subsingleton (HTot point (n + 1)) := subsingleton_quot _

private lemma point_colH : ¬ Subsingleton (colH point 0 0) := by
  refine not_subsingleton_of_notMem
    (x := (⟨fun _ => 1, rfl⟩ : LinearMap.ker (point.dV 0 0))) ?_
  change _ ∉ (⊥ : Submodule ℤ _)
  rw [Submodule.mem_bot]
  exact fun h => vec_one_ne_zero (congrArg Subtype.val h)

/-- The column hypothesis cannot be dropped: `point` has a nonzero total cohomology group. -/
example : ¬ ∀ (D : Bounded ℤ) (n : ℕ), Subsingleton (HTot D n) :=
  fun h => point_HTot_zero (h point 0)

example : ¬ ∀ p q, Subsingleton (colH point p q) := fun h => point_colH (h 0 0)

/-! The `E₂` pages of `point`, through `colHdH` and `transpose`. -/

example : ¬ Subsingleton (E₂I point 0 0) := by
  have : Subsingleton (point.C 1 0) := point.hBound 1 0 (by show 1 ≤ 1 ∨ 1 ≤ 0; omega)
  have : Subsingleton (colH point 1 0) := subsingleton_quot _
  refine not_subsingleton_of_notMem (x := (⟨Submodule.Quotient.mk ⟨fun _ => 1, rfl⟩,
    Subsingleton.elim _ _⟩ : LinearMap.ker (colHdH point 0 0))) ?_
  change _ ∉ (⊥ : Submodule ℤ _)
  rw [Submodule.mem_bot]
  intro h
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val h)
  change _ ∈ (⊥ : Submodule ℤ _) at h1
  exact vec_one_ne_zero (congrArg Subtype.val ((Submodule.mem_bot ℤ).1 h1))

example : ¬ Subsingleton (E₂II point 0 0) := by
  have : Subsingleton ((transpose point).C 1 0) := point.hBound 0 1 (by show 1 ≤ 0 ∨ 1 ≤ 1; omega)
  have : Subsingleton (colH (transpose point) 1 0) := subsingleton_quot _
  refine not_subsingleton_of_notMem (x := (⟨Submodule.Quotient.mk ⟨fun _ => 1, rfl⟩,
    Subsingleton.elim _ _⟩ : LinearMap.ker (colHdH (transpose point) 0 0))) ?_
  change _ ∉ (⊥ : Submodule ℤ _)
  rw [Submodule.mem_bot]
  intro h
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val h)
  change _ ∈ (⊥ : Submodule ℤ _) at h1
  exact vec_one_ne_zero (congrArg Subtype.val ((Submodule.mem_bot ℤ).1 h1))

example (D : Bounded ℤ) (a b : ℕ) : (transpose D).C a b = D.C b a := rfl

example (D : Bounded ℤ) (a b : ℕ) : (transpose D).dH a b = D.dV b a := rfl

example (D : Bounded ℤ) (a b : ℕ) : (transpose D).dV a b = D.dH b a := rfl

/-! The identity square `square 1 1 1 1`: exact columns, hence acyclic total complex. -/

private abbrev idSq : Bounded ℤ := square 1 1 1 1 rfl

/-- Both columns of the identity square are exact, through both branches of `colB`. -/
private lemma idSq_colH (p q : ℕ) : Subsingleton (colH idSq p q) := by
  by_cases hb : 2 ≤ p ∨ 2 ≤ q
  · have := idSq.hBound p q hb
    exact subsingleton_quot _
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨z, hz⟩ -
  obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
  all_goals obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
  all_goals first
    | exact ⟨z, funext fun i => one_mul (z i)⟩
    | (change _ ∈ (⊥ : Submodule ℤ _)
       rw [Submodule.mem_bot]
       refine Subtype.ext (funext fun i => ?_)
       have := congrFun (LinearMap.mem_ker.1 hz) i
       change 1 * z i = 0 at this
       simpa using this)

example (n : ℕ) : Subsingleton (HTot idSq n) :=
  subsingleton_HTot_of_forall_subsingleton_colH idSq idSq_colH n

/-- `HTotB D (n + 1)` contains the coboundaries: `(1, 1)` in degree one is `dTot` of `1`. -/
example : dTot idSq 0 (fun _ _ => 1) = fun _ _ => 1 := by
  funext ⟨⟨p, q⟩, h⟩ i
  rcases p with _ | _ | p <;> rcases q with _ | _ | q <;> try omega
  · rw [dTot_apply_zero_succ]; exact one_mul 1
  · rw [dTot_apply_succ_zero]; exact one_mul 1

/-! The zero-map square `square 0 0 0 0`: nonzero `H¹`. -/

private abbrev zsq : Bounded ℤ := square 0 0 0 0 rfl

private lemma zsq_dH (p q : ℕ) : zsq.dH p q = 0 := by
  rcases p with _ | _ | p <;> rcases q with _ | _ | q <;> simp [squareH]

private lemma zsq_dV (p q : ℕ) : zsq.dV p q = 0 := by
  rcases p with _ | _ | p <;> rcases q with _ | _ | q <;> simp [squareV]

private lemma zsq_dTot (n : ℕ) : dTot zsq n = 0 := by
  refine LinearMap.ext fun c => funext fun ⟨⟨p, q⟩, h⟩ => ?_
  rcases p with _ | p <;> rcases q with _ | q
  · omega
  · rw [dTot_apply_zero_succ, zsq_dV]; rfl
  · rw [dTot_apply_succ_zero, zsq_dH]; rfl
  · rw [dTot_apply_succ_succ, zsq_dH, zsq_dV]; simp

/-- `HTotB D (n + 1)` is not `⊤`: the class of `(1, 0)` in `H¹` is nonzero. -/
example : ¬ Subsingleton (HTot zsq 1) := by
  have hy : (Pi.single ⟨(1, 0), rfl⟩ (fun _ => 1) : Tot zsq 1) ∈ LinearMap.ker (dTot zsq 1) := by
    rw [LinearMap.mem_ker, zsq_dTot]; rfl
  refine not_subsingleton_of_notMem (x := (⟨_, hy⟩ : LinearMap.ker _)) ?_
  change _ ∉ (LinearMap.range (dTot zsq 0)).comap _
  rw [Submodule.mem_comap, zsq_dTot, LinearMap.range_zero, Submodule.mem_bot]
  intro h
  have := congrFun (congrFun h ⟨(1, 0), rfl⟩) 0
  simp only [Submodule.subtype_apply, Pi.single_eq_same] at this
  exact one_ne_zero this

/-! The horizontal identity `square 1 1 0 0`: `colHdH` and the `E₂I` page. -/

private abbrev hor : Bounded ℤ := square 1 1 0 0 rfl

private lemma hor_dV (p q : ℕ) : hor.dV p q = 0 := by
  rcases p with _ | _ | p <;> rcases q with _ | _ | q <;> simp [squareV]

private noncomputable def horClass (p : ℕ) (v : hor.C p 0) : colH hor p 0 :=
  Submodule.Quotient.mk ⟨v, by rw [LinearMap.mem_ker, hor_dV]; rfl⟩

private lemma colHdH_horClass (v : hor.C 0 0) : colHdH hor 0 0 (horClass 0 v) = horClass 1 v := by
  simp only [horClass, colHdH, Submodule.mapQ_apply]
  congr 1
  exact Subtype.ext (funext fun i => one_mul (v i))

/-- `colHdH` is induced by the horizontal map (here the identity), so it is nonzero. -/
example : colHdH hor 0 0 (horClass 0 fun _ => 1) ≠ 0 := by
  rw [colHdH_horClass, horClass, Ne, Submodule.Quotient.mk_eq_zero]
  change _ ∉ (⊥ : Submodule ℤ _)
  rw [Submodule.mem_bot]
  exact fun h => vec_one_ne_zero (congrArg Subtype.val h)

/-- `E₂IB D (p + 1)` is the image of `colHdH`, so `E₂I` of the horizontal identity vanishes. -/
example : Subsingleton (E₂I hor 1 0) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨k, hk⟩ -
  change k ∈ LinearMap.range (colHdH hor 0 0)
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ k
  refine ⟨horClass 0 w.1, ?_⟩
  rw [colHdH_horClass, horClass]

/-! The zero complex, at the boundary `N = 0`, and the theorem's general signature. -/

private abbrev zeroComplex : Bounded ℤ where
  C _ _ := Fin 0 → ℤ
  dH _ _ := 0
  dV _ _ := 0
  dH_sq _ _ := LinearMap.zero_comp _
  dV_sq _ _ := LinearMap.zero_comp _
  dHV_comm _ _ := rfl
  N := 0
  hBound _ _ _ := inferInstance

example (n : ℕ) : Subsingleton (HTot zeroComplex n) :=
  subsingleton_HTot_of_forall_subsingleton_colH zeroComplex (fun _ _ => subsingleton_quot _) n

example {R : Type u} [CommRing R] (D : Bounded R) (h : ∀ p q : ℕ, Subsingleton (colH D p q))
    (n : ℕ) : Subsingleton (HTot D n) :=
  subsingleton_HTot_of_forall_subsingleton_colH D h n

end DoubleComplexBoundedTest
