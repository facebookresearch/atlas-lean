/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_DoubleComplex.lean`
and
`Theorems/Thm_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH.lean`
and
`P2M/Sol/S_DoubleComplex_subsingleton_HTot_of_forall_subsingleton_colH.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import MathlibExt.Algebra.Homology.BoundedDoubleComplex

/-!
# Total cohomology of bounded double complexes

For a bounded first-quadrant double complex `D : DoubleComplex.Bounded R` of `R`-modules, from
`MathlibExt.Algebra.Homology.BoundedDoubleComplex`, this file defines the cohomology of its
total complex, the cohomology of its columns, its transpose and its two `E₂` pages, and proves
that the total complex is acyclic when every column is.

## Conventions

* The indexing is cohomological and first-quadrant: `D.C p q` is the term in column `p` and
  row `q` for `p q : ℕ`, the horizontal differential `D.dH p q` raises `p` and the vertical
  differential `D.dV p q` raises `q`.
* `D.N` bounds the support: `D.hBound` says that `D.C p q` is a subsingleton (a zero module)
  whenever `D.N ≤ p` or `D.N ≤ q`.
* The total complex is `Tot D n = ∏_{p + q = n} D.C p q` with differential
  `dTot D n = dH + (-1) ^ p • dV`: the vertical part of `dTot` in column `p` carries the sign
  `(-1) ^ p`, and the horizontal part carries no sign.
* No differential enters degree `0`: `HTotB D 0 = ⊥`, `colB D p 0 = ⊥` and `E₂IB D 0 q = ⊥`,
  so in degree `0` the groups `HTot D 0`, `colH D p 0` and `E₂I D 0 q` are the kernels of
  `dTot D 0`, `D.dV p 0` and `colHdH D 0 q` modulo `⊥`.
* `E₂I D p q` takes vertical cohomology first and horizontal cohomology second, at bidegree
  `(p, q)`. `E₂II D p q`, defined as `E₂I (transpose D) q p`, takes horizontal cohomology
  first and vertical cohomology second, at the same bidegree `(p, q)` of `D`.

## Main results

* `DoubleComplex.subsingleton_HTot_of_forall_subsingleton_colH`: if every column cohomology
  group `colH D p q` vanishes, then every total cohomology group `HTot D n` vanishes. This is
  a case of the acyclic assembly lemma (Weibel, *An Introduction to Homological Algebra*,
  Lemma 2.7.3).
-/

@[expose] public section

universe u

namespace DoubleComplex

section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)

/-- The coboundaries of the total complex, as a submodule of the cocycles
`LinearMap.ker (dTot D n)`: in degree `n' + 1` the cocycles that lie in the image of
`dTot D n'`, and `⊥` in degree `0`, which no differential enters. -/
def HTotB : (n : ℕ) → Submodule R (LinearMap.ker (dTot D n))
  | 0 => ⊥
  | n' + 1 => (LinearMap.range (dTot D n')).comap
      (LinearMap.ker (dTot D (n' + 1))).subtype

/-- The total cohomology group in degree `n`: the cocycles of `dTot D n` modulo the
coboundaries `HTotB D n`. -/
abbrev HTot (n : ℕ) : Type u :=
  LinearMap.ker (dTot D n) ⧸ HTotB D n

end Tot

section E2

variable {R : Type u} [CommRing R] (D : Bounded R)

/-- The vertical coboundaries in column `p`, as a submodule of the vertical cocycles
`LinearMap.ker (D.dV p q)`: in row `q' + 1` the cocycles that lie in the image of
`D.dV p q'`, and `⊥` in row `0`, which no vertical differential enters. -/
def colB (p : ℕ) : (q : ℕ) → Submodule R (LinearMap.ker (D.dV p q))
  | 0 => ⊥
  | q' + 1 => (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype

/-- The cohomology of column `p` in row `q`: the vertical cocycles `LinearMap.ker (D.dV p q)`
modulo the vertical coboundaries `colB D p q`. -/
abbrev colH (p q : ℕ) : Type u :=
  LinearMap.ker (D.dV p q) ⧸ colB D p q

/-- The map `colH D p q →ₗ[R] colH D (p + 1) q` induced by the horizontal differential
`D.dH p q`, which maps vertical cocycles to vertical cocycles and vertical coboundaries to
vertical coboundaries because the two differentials commute. -/
def colHdH (p q : ℕ) :
    colH D p q →ₗ[R] colH D (p + 1) q :=
  Submodule.mapQ _ _
    ((D.dH p q).restrict fun x hx => LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply,
        LinearMap.mem_ker.mp hx, map_zero])
    (by
      rcases q with _ | q'
      · simp only [colB]; exact bot_le
      · rintro x ⟨y, hy⟩
        exact ⟨D.dH p q' y, by
          change D.dV (p + 1) q' (D.dH p q' y) = D.dH p (q' + 1) x.1
          rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply, hy]; rfl⟩)

/-- The coboundaries for `colHdH` at bidegree `(p, q)`, as a submodule of
`LinearMap.ker (colHdH D p q)`: in column `p' + 1` the elements of that kernel that lie in the
image of `colHdH D p' q`, and `⊥` in column `0`. -/
def E₂IB :
    (p q : ℕ) → Submodule R (LinearMap.ker (colHdH D p q))
  | 0, _ => ⊥
  | p' + 1, q => (LinearMap.range (colHdH D p' q)).comap
      (LinearMap.ker (colHdH D (p' + 1) q)).subtype

/-- The `E₂` term at bidegree `(p, q)` that takes vertical cohomology first and horizontal
cohomology second: the kernel of `colHdH D p q` modulo `E₂IB D p q`, which is the cohomology
of `colHdH` at `colH D p q`. -/
abbrev E₂I (p q : ℕ) : Type u :=
  LinearMap.ker (colHdH D p q) ⧸ E₂IB D p q

/-- The transpose of `D`: `(transpose D).C a b = D.C b a`, with the horizontal and vertical
differentials exchanged and the same bound `D.N`. -/
def transpose : Bounded R where
  C a b := D.C b a
  dH a b := D.dV b a
  dV a b := D.dH b a
  dH_sq a b := D.dV_sq b a
  dV_sq a b := D.dH_sq b a
  dHV_comm a b := (D.dHV_comm b a).symm
  N := D.N
  hBound a b h := D.hBound b a h.symm

/-- The `E₂` term at bidegree `(p, q)` of `D` that takes horizontal cohomology first and
vertical cohomology second, defined as `E₂I (transpose D) q p`: the rows of `D` are the columns
of `transpose D`. -/
abbrev E₂II (p q : ℕ) : Type u :=
  E₂I (transpose D) q p

instance (p q : ℕ) : AddCommGroup (E₂I D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂I D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))
instance (p q : ℕ) : AddCommGroup (E₂II D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂II D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))

end E2

section Proof


variable {R : Type u} [CommRing R] (D : Bounded R)

private theorem eq_zero_of_neg_one_pow_smul_eq_zero {M : Type u} [AddCommGroup M] (m : ℕ) (x : M)
    (hx : ((-1 : ℤ) ^ m) • x = 0) : x = 0 := by
  rcases neg_one_pow_eq_or ℤ m with h | h <;> rw [h] at hx <;> simpa using hx

private theorem neg_one_pow_smul_neg_one_pow_smul {M : Type u} [AddCommGroup M] (m : ℕ) (x : M) :
    ((-1 : ℤ) ^ m) • (((-1 : ℤ) ^ m) • x) = x := by
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

open Classical in
private theorem dTot_single_vert {n k q' : ℕ} (hk : k + q' = n) (w : D.C k q')
    (h : k + (q' + 1) = n + 1) :
    dTot D n (Pi.single (⟨(k, q'), hk⟩ : Diag n) w) ⟨(k, q' + 1), h⟩
      = ((-1 : ℤ) ^ k) • D.dV k q' w := by
  cases k with
  | zero =>
    rw [dTot_apply_zero_succ, pow_zero, one_smul]
    congr 1
    exact Pi.single_eq_same _ _
  | succ k' =>
    rw [dTot_apply_succ_succ]
    have h1 : (Pi.single (⟨(k' + 1, q'), hk⟩ : Diag n) w : Tot D n) ⟨(k', q' + 1), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg (fun i : Diag n => i.1.1) e
        simp only at this
        omega) _
    have h2 : (Pi.single (⟨(k' + 1, q'), hk⟩ : Diag n) w : Tot D n) ⟨(k' + 1, q'), by omega⟩ = w :=
      Pi.single_eq_same _ _
    rw [h1, h2, map_zero, zero_add]

open Classical in
private theorem dTot_single_eq_zero {n k q' : ℕ} (hk : k + q' = n) (w : D.C k q') (j : Diag (n + 1))
    (hj : j.1.1 ≤ k) (hj' : ¬ (j.1.1 = k ∧ j.1.2 = q' + 1)) :
    dTot D n (Pi.single (⟨(k, q'), hk⟩ : Diag n) w) j = 0 := by
  obtain ⟨⟨p, r⟩, hpr⟩ := j
  simp only at hj hj' hpr
  rcases p with _ | p' <;> rcases r with _ | r'
  · exfalso; omega
  · rw [dTot_apply_zero_succ]
    have e : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(0, r'), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e, map_zero]
  · rw [dTot_apply_succ_zero]
    have e : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p', 0), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e, map_zero]
  · rw [dTot_apply_succ_succ]
    have e1 : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p', r' + 1), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    have e2 : (Pi.single (⟨(k, q'), hk⟩ : Diag n) w : Tot D n) ⟨(p' + 1, r'), by omega⟩ = 0 :=
      Pi.single_eq_of_ne (fun e => by
        have := congrArg Subtype.val e
        simp only [Prod.mk.injEq] at this
        omega) _
    rw [e1, e2, map_zero, map_zero, smul_zero, add_zero]

open Classical in
private theorem stair (n : ℕ)
    (hcol0 : ∀ (p : ℕ) (z : D.C p 0), D.dV p 0 z = 0 → z = 0)
    (hcolS : ∀ (p q' : ℕ) (z : D.C p (q' + 1)), D.dV p (q' + 1) z = 0 → ∃ y, D.dV p q' y = z)
    (c : Tot D (n + 1)) (hc : dTot D (n + 1) c = 0) (k : ℕ) :
    ∃ b : Tot D n, ∀ i : Diag (n + 1), i.1.1 < k → (c - dTot D n b) i = 0 := by
  induction k with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨b, hb⟩ := ih
    by_cases hk : n + 1 < k
    · exact ⟨b, fun i hi => hb i (by have := i.2; omega)⟩
    obtain ⟨q, hq⟩ : ∃ q, k + q = n + 1 := ⟨n + 1 - k, by omega⟩
    have hcyc : dTot D (n + 1) (c - dTot D n b) = 0 := by
      rw [map_sub, hc, zero_sub, neg_eq_zero]
      simpa using LinearMap.congr_fun (dTot_comp_dTot D n) b
    have KV : D.dV k q ((c - dTot D n b) ⟨(k, q), hq⟩) = 0 := by
      cases k with
      | zero =>
        have e := congrFun hcyc ⟨(0, q + 1), by omega⟩
        rw [dTot_apply_zero_succ, Pi.zero_apply] at e
        exact e
      | succ k' =>
        have e := congrFun hcyc ⟨(k' + 1, q + 1), by omega⟩
        rw [dTot_apply_succ_succ, Pi.zero_apply, hb ⟨(k', q + 1), by omega⟩ (Nat.lt_succ_self _),
          map_zero, zero_add] at e
        exact eq_zero_of_neg_one_pow_smul_eq_zero _ _ e
    cases q with
    | zero =>
      refine ⟨b, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · exact hb i hlt
      · have hi2 : i = ⟨(k, 0), hq⟩ :=
          Subtype.ext (Prod.ext heq (by have h2 := i.2; dsimp only at h2 heq ⊢; omega))
        rw [hi2]
        exact hcol0 k _ KV
    | succ q' =>
      obtain ⟨y, hy⟩ := hcolS k q' _ KV
      refine ⟨b + Pi.single (⟨(k, q'), by omega⟩ : Diag n) (((-1 : ℤ) ^ k) • y), fun i hi => ?_⟩
      rw [map_add, ← sub_sub, Pi.sub_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · rw [hb i hlt, dTot_single_eq_zero D _ _ i hlt.le (fun h => by omega), sub_zero]
      · have hi2 : i = ⟨(k, q' + 1), hq⟩ :=
          Subtype.ext (Prod.ext heq (by have h2 := i.2; dsimp only at h2 heq ⊢; omega))
        rw [hi2, dTot_single_vert D, map_zsmul, neg_one_pow_smul_neg_one_pow_smul, hy, sub_self]

/-- **Acyclic assembly for bounded double complexes.** If every column cohomology group
`colH D p q` of a bounded first-quadrant double complex vanishes (as a subsingleton), then
every total cohomology group `HTot D n` vanishes. In row `0` the hypothesis says that each
`D.dV p 0` is injective, and in degree `0` the conclusion says that `dTot D 0` is injective.
The bound `D.N` plays no role: each antidiagonal `p + q = n` is finite, so the same holds for
every first-quadrant double complex. This is a case of the acyclic assembly lemma (Weibel,
*An Introduction to Homological Algebra*, Lemma 2.7.3). -/
theorem subsingleton_HTot_of_forall_subsingleton_colH
    (h : ∀ p q : ℕ, Subsingleton (colH D p q)) (n : ℕ) :
    Subsingleton (HTot D n) := by
  classical
  have hcol : ∀ (p q : ℕ) (z : LinearMap.ker (D.dV p q)), z ∈ colB D p q := fun p q z =>
    (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  have hcol0 : ∀ (p : ℕ) (z : D.C p 0), D.dV p 0 z = 0 → z = 0 := fun p z hz => by
    have e := hcol p 0 ⟨z, LinearMap.mem_ker.2 hz⟩
    change _ ∈ (⊥ : Submodule R _) at e
    rw [Submodule.mem_bot] at e
    exact congrArg Subtype.val e
  have hcolS : ∀ (p q' : ℕ) (z : D.C p (q' + 1)), D.dV p (q' + 1) z = 0 → ∃ y, D.dV p q' y = z :=
    fun p q' z hz => by
    have e := hcol p (q' + 1) ⟨z, LinearMap.mem_ker.2 hz⟩
    change _ ∈ (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype at e
    rw [Submodule.mem_comap, LinearMap.mem_range] at e
    exact e
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨c, hc⟩ -
  cases n with
  | zero =>
    change (⟨c, hc⟩ : LinearMap.ker (dTot D 0)) ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    apply Subtype.ext
    change c = 0
    funext i
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    have hp : p = 0 := by simp only at hpq; omega
    have hq : q = 0 := by simp only at hpq; omega
    subst hp hq
    have e := congrFun (LinearMap.mem_ker.1 hc) ⟨(0, 1), by omega⟩
    rw [dTot_apply_zero_succ, Pi.zero_apply] at e
    exact hcol0 0 _ e
  | succ n =>
    obtain ⟨b, hb⟩ := stair D n hcol0 hcolS c (LinearMap.mem_ker.1 hc) (n + 2)
    change (⟨c, hc⟩ : LinearMap.ker (dTot D (n + 1))) ∈
      (LinearMap.range (dTot D n)).comap (LinearMap.ker (dTot D (n + 1))).subtype
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨b, ?_⟩
    change dTot D n b = c
    have e : c - dTot D n b = 0 := funext fun i => hb i (by have := i.2; omega)
    exact (sub_eq_zero.1 e).symm


end Proof

end DoubleComplex
