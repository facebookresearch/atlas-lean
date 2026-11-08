/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.BurnsidePaqb.SolvableInduction
public import MathlibExt.GroupTheory.BurnsidePaqb.SimplePrime

/-!
# Burnside's `p^a q^b` theorem: groups of order `p ^ a * q ^ b` are solvable

Authors: Muse Spark 1.3

Port of the fully proved headline stage from the screened archive
`genai_web_search/tree/users/akiezun/burnside_proof.zip` (SHA-256
`d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00`):
`Burnside/Statement.lean`.

Historical note: the character-theoretic argument follows the Bielefeld-hosted
note `https://www.math.uni-bielefeld.de/~sek/select/rw3.pdf` (SHA-256
`24d40da9224a30699cf9fe50b7e1abedeb2e7b2bbfdb6d273e0073fb222dd703`), and the
original result is W. Burnside, "On Groups of Order p^alpha q^beta,"
*Proceedings of the London Mathematical Society* s2-1 (1904), 388–392,
DOI `10.1112/plms/s2-1.1.388`.

The formal statement permits the boundary conventions `p = q` and zero
exponents (covering `p`-groups and the trivial group); these conveniences are
formal and are not attributed to the historical source.
-/

namespace BurnsidePaqb

@[expose] public section

universe u

/-- Burnside's `p^a q^b` theorem for small-universe groups: if `G` is finite with
`Fintype.card G = p ^ a * q ^ b` for primes `p, q`, then `G` is solvable.
Proved via the simple-prime-power corollary and induction. -/
theorem burnside_paqb_zero {G : Type} [Group G] [Fintype G]
    (p q : ℕ) (a b : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hcard : Fintype.card G = p ^ a * q ^ b) : Group.IsSolvable G :=
  burnside_paqb_of_simple_prime
    (fun hH hg => by
      have := hH
      obtain ⟨g, hg1, hpp⟩ := hg
      exact cor6_of_prime_pow_class g hg1 hpp)
    p q a b hp hq hcard

attribute [-instance] Fin.instMul in
/-- If `G` is finite and `Fintype.card G = p ^ a * q ^ b` for primes `p, q` and
`a, b : ℕ`, then `G` is solvable. Proved by descent to `Fin (Fintype.card G)`. -/
theorem burnside_paqb {G : Type*} [Group G] [Fintype G]
    (p q a b : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hcard : Fintype.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  classical
  set n := Fintype.card G with hn
  set e : G ≃ Fin n := Fintype.equivFin G with he
  let mulFin : Mul (Fin n) := ⟨fun x y => e (e.symm x * e.symm y)⟩
  let oneFin : One (Fin n) := ⟨e 1⟩
  let invFin : Inv (Fin n) := ⟨fun x => e (e.symm x)⁻¹⟩
  let divFin : Div (Fin n) := ⟨fun x y => e (e.symm x / e.symm y)⟩
  let npowFin : Pow (Fin n) ℕ := ⟨fun x k => e (e.symm x ^ k)⟩
  let zpowFin : Pow (Fin n) ℤ := ⟨fun x k => e (e.symm x ^ k)⟩
  have hone : e.symm oneFin.one = 1 := by
    rw [show oneFin.one = e 1 from rfl]
    exact e.symm_apply_apply 1
  have hmul : ∀ x y : Fin n, e.symm (x * y) = e.symm x * e.symm y :=
    fun x y => e.symm_apply_apply _
  have hinv : ∀ x : Fin n, e.symm x⁻¹ = (e.symm x)⁻¹ :=
    fun x => e.symm_apply_apply _
  have hdiv : ∀ x y : Fin n, e.symm (x / y) = e.symm x / e.symm y :=
    fun x y => e.symm_apply_apply _
  have hnpow : ∀ (x : Fin n) (k : ℕ), e.symm (x ^ k) = e.symm x ^ k := by
    intro x k
    rw [show (x ^ k) = e (e.symm x ^ k) from rfl]
    exact e.symm_apply_apply _
  have hzpow : ∀ (x : Fin n) (k : ℤ), e.symm (x ^ k) = e.symm x ^ k := by
    intro x k
    rw [show (x ^ k) = e (e.symm x ^ k) from rfl]
    exact e.symm_apply_apply _
  let : Group (Fin n) := Function.Injective.group (e.symm : Fin n → G)
    e.symm.injective hone hmul hinv hdiv hnpow hzpow
  have hcardH : Fintype.card (Fin n) = p ^ a * q ^ b := by
    rw [Fintype.card_fin]
    exact hcard
  have hsolH : Group.IsSolvable (Fin n) := burnside_paqb_zero p q a b hp hq hcardH
  let E : (Fin n) →* G :=
    { toFun := e.symm, map_one' := hone, map_mul' := hmul }
  have hEsurj : Function.Surjective E := fun b => ⟨e b, e.symm_apply_apply b⟩
  have hrange : E.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hx⟩ := hEsurj y
    exact ⟨x, hx⟩
  let T : G →* Unit :=
    { toFun := fun _ => (), map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hle : T.ker ≤ E.range := by
    rw [hrange]
    exact le_top
  have := hsolH
  exact Group.isSolvable_of_ker_le_range E T hle

end

end BurnsidePaqb
