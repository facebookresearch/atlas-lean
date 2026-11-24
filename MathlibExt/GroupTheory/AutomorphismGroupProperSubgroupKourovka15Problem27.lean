/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-!
# A p-group and a proper subgroup with isomorphic automorphism groups

We prove the affirmative answer to Kourovka Notebook Problem 15.27 using the semidirect product
of an elementary abelian group of order eight by a cyclic group of order four. The subgroup
uses the square of the cyclic generator. A six-bit normal form describes both automorphism
groups. We check the generator actions, the normal form's coverage and the right
multiplication rules by finite computation in the kernel.
-/

namespace MathlibExt.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.27 (Ya. G.
Berkovich). UnsolvedMath record UM-00701115 (`KOU-15.27`), dataset ulamai/UnsolvedMath v1.8.0.

The target asks for some prime `p`. The bound `|G| > 2` excludes `G` of order `2` with `H = 1`.
`Aut` is `MulAut`, compared by a group isomorphism.
-/

/-- **Berkovich's problem on automorphism groups of p-groups (Kourovka 15.27).** The statement that
for some prime $p$ there are a finite $p$-group $G$ of order greater than $2$ and a proper subgroup
$H < G$ whose automorphism groups are isomorphic, $\mathrm{Aut}(G) \cong \mathrm{Aut}(H)$. -/
@[expose] public def autIsoAutOfProperSubgroup : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ 2 < Nat.card G ∧
    ∃ H : Subgroup G, H ≠ ⊤ ∧ Nonempty (MulAut G ≃* MulAut H)

open scoped commutatorElement

private abbrev V := Multiplicative (Fin 2 × Fin 2 × Fin 2)
private abbrev C (n : ℕ) := Multiplicative (Fin n)

private def low (t : Fin 4) : Fin 2 := Fin.ofNat _ t.val
private def high (t : Fin 4) : Fin 2 := Fin.ofNat _ (t.val / 2)

/-- The powers of the unipotent Jordan block on three bits. -/
private def shift (t : C 4) (v : V) : V :=
  let (x, y, z) := v.toAdd
  Multiplicative.ofAdd (x, y + low t.toAdd * x, z + low t.toAdd * y + high t.toAdd * x)

private def shiftAut (t : C 4) : MulAut V where
  toFun := shift t
  invFun := shift t⁻¹
  left_inv := (by decide +kernel : ∀ (t : C 4) (v : V), shift t⁻¹ (shift t v) = v) t
  right_inv := (by decide +kernel : ∀ (t : C 4) (v : V), shift t (shift t⁻¹ v) = v) t
  map_mul' := (by decide +kernel :
    ∀ (t : C 4) (u v : V), shift t (u * v) = shift t u * shift t v) t

private def action : C 4 →* MulAut V where
  toFun := shiftAut
  map_one' := MulEquiv.ext (by decide +kernel : ∀ v : V, shift 1 v = v)
  map_mul' t s := MulEquiv.ext
    ((by decide +kernel : ∀ (t s : C 4) (v : V), shift (t * s) v = shift t (shift s v)) t s)

private def double : C 2 →* C 4 where
  toFun t := Multiplicative.ofAdd (Fin.ofNat _ (2 * t.toAdd.val))
  map_one' := rfl
  map_mul' := by decide +kernel

private abbrev G := V ⋊[action] C 4
private abbrev H := V ⋊[action.comp double] C 2

private instance instFintypeG : Fintype G :=
  Fintype.ofEquiv (V × C 4) SemidirectProduct.equivProd.symm

private instance instFintypeH : Fintype H :=
  Fintype.ofEquiv (V × C 2) SemidirectProduct.equivProd.symm

private def embed : H →* G where
  toFun v := ⟨v.left, double v.right⟩
  map_one' := rfl
  map_mul' u v := SemidirectProduct.ext rfl (map_mul double u.right v.right)

private theorem embed_injective : Function.Injective embed := by
  have hd : ∀ u v : C 2, double u = double v → u = v := by decide +kernel
  intro u v h
  exact SemidirectProduct.ext (congrArg (fun x : G ↦ x.left) h)
    (hd _ _ (congrArg (fun x : G ↦ x.right) h))

private def gElt (x y z : Fin 2) (t : Fin 4) : G :=
  ⟨Multiplicative.ofAdd (x, y, z), Multiplicative.ofAdd t⟩

private def hElt (x y z t : Fin 2) : H :=
  ⟨Multiplicative.ofAdd (x, y, z), Multiplicative.ofAdd t⟩

-- In the larger group, the other two basis vectors are commutators with the cyclic generator.
-- In the smaller group, only the third basis vector is such a commutator, and hb is central.
private def gx : G := gElt 1 0 0 0
private def gy : G := gElt 0 0 0 1
private def hx : H := hElt 1 0 0 0
private def hb : H := hElt 0 1 0 0
private def hw : H := hElt 0 0 0 1

private theorem gAut_ext {f g : MulAut G} (ex : f gx = g gx) (ey : f gy = g gy) : f = g := by
  have hform : ∀ v : G,
      v = gx ^ v.left.toAdd.1.val * ⁅gy, gx⁆ ^ v.left.toAdd.2.1.val *
        ⁅gy, ⁅gy, gx⁆⁆ ^ v.left.toAdd.2.2.val * gy ^ v.right.toAdd.val := by
    decide +kernel
  apply MulEquiv.ext
  intro v
  conv_lhs => rw [hform v]
  conv_rhs => rw [hform v]
  simp only [map_mul, map_pow, map_commutatorElement, ex, ey]

private theorem hAut_ext {f g : MulAut H} (ex : f hx = g hx) (eb : f hb = g hb)
    (ew : f hw = g hw) : f = g := by
  have hform : ∀ v : H,
      v = hx ^ v.left.toAdd.1.val * hb ^ v.left.toAdd.2.1.val *
        ⁅hw, hx⁆ ^ v.left.toAdd.2.2.val * hw ^ v.right.toAdd.val := by
    decide +kernel
  apply MulEquiv.ext
  intro v
  conv_lhs => rw [hform v]
  conv_rhs => rw [hform v]
  simp only [map_mul, map_pow, map_commutatorElement, ex, eb, ew]

/-- Each of six involutions occurs with exponent zero or one in a normal form. -/
private structure Code where
  a : Fin 2
  b : Fin 2
  c : Fin 2
  d : Fin 2
  e : Fin 2
  f : Fin 2
  deriving DecidableEq, Fintype

/-- The six generator actions on the group of order 32, in normal form order. -/
private def gAction (i : Fin 6) (v : G) : G :=
  let (x, y, z) := v.left.toAdd
  let t := v.right.toAdd
  let r := low t
  let s := high t
  match i with
  | 0 => gElt (x + r) (y + r + s) (z + s + r * s) t
  | 1 => gElt x (y + r) (z + s) t
  | 2 => gElt x y (z + y) (-t)
  | 3 => gElt x y (z + r) t
  | 4 => gElt x y (z + x) t
  | 5 => gElt x (y + x) (z + x) (-t)

/-- The corresponding six generator actions on the group of order 16. -/
private def hAction (i : Fin 6) (v : H) : H :=
  let (x, y, z) := v.left.toAdd
  let t := v.right.toAdd
  match i with
  | 0 => hElt x y (z + y) t
  | 1 => hElt x y (z + t) t
  | 2 => hElt x (y + t) (z + t) t
  | 3 => hElt x y (z + x + t) t
  | 4 => hElt x (y + x + t) (z + x + t) t
  | 5 => hElt t (x + y + t) (x + z + t + x * t) x

private def involutionAut {A : Type} [Group A] (f : A → A)
    (hf : Function.Involutive f) (hm : ∀ x y, f (x * y) = f x * f y) : MulAut A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf
  map_mul' := hm

set_option maxHeartbeats 2000000 in
-- The multiplication check runs over all pairs of group elements for each generator.
private def gBasis (i : Fin 6) : MulAut G :=
  involutionAut (gAction i)
    ((by decide +kernel : ∀ (i : Fin 6) (v : G), gAction i (gAction i v) = v) i)
    ((by decide +kernel :
      ∀ (i : Fin 6) (u v : G), gAction i (u * v) = gAction i u * gAction i v) i)

set_option maxHeartbeats 2000000 in
-- The multiplication check runs over all pairs of group elements for each generator.
private def hBasis (i : Fin 6) : MulAut H :=
  involutionAut (hAction i)
    ((by decide +kernel : ∀ (i : Fin 6) (v : H), hAction i (hAction i v) = v) i)
    ((by decide +kernel :
      ∀ (i : Fin 6) (u v : H), hAction i (u * v) = hAction i u * hAction i v) i)

private def word {A : Type} [Monoid A] (basis : Fin 6 → A) (q : Code) : A :=
  basis 0 ^ q.a.val * basis 1 ^ q.b.val * basis 2 ^ q.c.val * basis 3 ^ q.d.val *
    basis 4 ^ q.e.val * basis 5 ^ q.f.val

/-- Right multiplication of a normal form by the given generator. -/
private def step (q : Code) (i : Fin 6) : Code :=
  match i with
  | 0 => { q with a := q.a + 1, b := q.b + q.c, d := q.d + q.e + q.f }
  | 1 => { q with b := q.b + 1, d := q.d + q.f }
  | 2 => { q with c := q.c + 1, e := q.e + q.f }
  | 3 => { q with d := q.d + 1 }
  | 4 => { q with e := q.e + 1 }
  | 5 => { q with f := q.f + 1 }

private theorem gStep (q : Code) (i : Fin 6) :
    word gBasis (step q i) = word gBasis q * gBasis i := by
  have h : ∀ (q : Code) (i : Fin 6),
      word gBasis (step q i) gx = word gBasis q (gBasis i gx) ∧
        word gBasis (step q i) gy = word gBasis q (gBasis i gy) := by
    decide +kernel
  exact gAut_ext (h q i).1 (h q i).2

private theorem hStep (q : Code) (i : Fin 6) :
    word hBasis (step q i) = word hBasis q * hBasis i := by
  have h : ∀ (q : Code) (i : Fin 6),
      word hBasis (step q i) hx = word hBasis q (hBasis i hx) ∧
        word hBasis (step q i) hb = word hBasis q (hBasis i hb) ∧
        word hBasis (step q i) hw = word hBasis q (hBasis i hw) := by
    decide +kernel
  exact hAut_ext (h q i).1 (h q i).2.1 (h q i).2.2

private def stepPow (i : Fin 6) (b : Fin 2) (q : Code) : Code :=
  if b = 0 then q else step q i

private def mulCode (q p : Code) : Code :=
  q |> stepPow 0 p.a |> stepPow 1 p.b |> stepPow 2 p.c |> stepPow 3 p.d |>
    stepPow 4 p.e |> stepPow 5 p.f

private theorem word_mulCode {A : Type} [Monoid A] (basis : Fin 6 → A)
    (hstep : ∀ q i, word basis (step q i) = word basis q * basis i) (q p : Code) :
    word basis (mulCode q p) = word basis q * word basis p := by
  have hpow (i : Fin 6) (b : Fin 2) (q : Code) :
      word basis (stepPow i b q) = word basis q * basis i ^ b.val := by
    fin_cases b
    · simp [stepPow]
    · simpa [stepPow] using hstep q i
  simp only [mulCode, hpow]
  conv_rhs => arg 2; unfold word
  simp only [mul_assoc]

/-- Decode the images of the two generators of the group of order 32. -/
private def gDecode (u v : G) : Code :=
  let a := u.left.toAdd.2.1
  let b := u.left.toAdd.2.2
  let (c, d, e) := v.left.toAdd
  let f := high v.right.toAdd
  ⟨c, c + d + c * f, a + f, e + d * f, b + a * f, a⟩

/-- Decode the images of the three generators of the group of order 16. -/
private def hDecode (u v w : H) : Code :=
  let a := u.right.toAdd
  let b := u.left.toAdd.2.1
  let c := u.left.toAdd.2.2
  let d := w.left.toAdd.2.1
  let e := w.left.toAdd.2.2
  let f := v.left.toAdd.2.2
  let t := b + c + d + e + (b + d) * f
  ⟨f, t, b + d, b + c + a * t + b * f, a + b + a * (b + d), a⟩

private theorem gWord_bijective : Function.Bijective (word gBasis) := by
  constructor
  · have h : ∀ q : Code, gDecode (word gBasis q gx) (word gBasis q gy) = q := by decide +kernel
    intro q p eq
    rw [← h q, eq, h p]
  · intro f
    -- The first generator is an involution with a nontrivial iterated commutator with the second.
    have h : ∀ u v : G, (! (decide (u * u = 1) && decide (⁅v, ⁅v, u⁆⁆ ≠ 1)) ||
        (decide (word gBasis (gDecode u v) gx = u) &&
          decide (word gBasis (gDecode u v) gy = v))) = true := by
      decide +kernel
    have hu : f gx * f gx = 1 := by
      rw [← map_mul, show gx * gx = 1 by decide, map_one]
    have hv : ⁅f gy, ⁅f gy, f gx⁆⁆ ≠ 1 := by
      rw [← map_commutatorElement, ← map_commutatorElement, ← map_one f]
      exact fun e ↦ (by decide : ⁅gy, ⁅gy, gx⁆⁆ ≠ 1) (f.injective e)
    let q := gDecode (f gx) (f gy)
    have himages : word gBasis q gx = f gx ∧ word gBasis q gy = f gy := by
      simpa [hu, hv, q] using h (f gx) (f gy)
    exact ⟨q, gAut_ext himages.1 himages.2⟩

set_option maxHeartbeats 2000000 in
-- Coverage checks the possible images of three generators.
private theorem hWord_bijective : Function.Bijective (word hBasis) := by
  constructor
  · have h : ∀ q : Code,
        hDecode (word hBasis q hx) (word hBasis q hb) (word hBasis q hw) = q := by
      decide +kernel
    intro q p eq
    rw [← h q, eq, h p]
  · intro f
    -- The two noncommuting involutions and the extra central generator determine the images.
    have h : ∀ u v w : H,
        (! (decide (u * u = 1) && decide (w * w = 1) && decide (⁅w, u⁆ ≠ 1) &&
          decide (v ≠ 1) && decide (v ≠ ⁅w, u⁆) && decide (v * hx = hx * v) &&
          decide (v * hw = hw * v)) ||
          (decide (word hBasis (hDecode u v w) hx = u) &&
            decide (word hBasis (hDecode u v w) hb = v) &&
            decide (word hBasis (hDecode u v w) hw = w))) = true := by
      decide +kernel
    have hu : f hx * f hx = 1 := by
      rw [← map_mul, show hx * hx = 1 by decide, map_one]
    have hw' : f hw * f hw = 1 := by
      rw [← map_mul, show hw * hw = 1 by decide, map_one]
    have hc : ⁅f hw, f hx⁆ ≠ 1 := by
      rw [← map_commutatorElement, ← map_one f]
      exact fun e ↦ (by decide : ⁅hw, hx⁆ ≠ 1) (f.injective e)
    have hb₁ : f hb ≠ 1 := by
      rw [← map_one f]
      exact fun e ↦ (by decide : hb ≠ 1) (f.injective e)
    have hb₂ : f hb ≠ ⁅f hw, f hx⁆ := by
      rw [← map_commutatorElement]
      exact fun e ↦ (by decide : hb ≠ ⁅hw, hx⁆) (f.injective e)
    have hcentral (v : H) : f hb * v = v * f hb := by
      have hbv : ∀ v : H, hb * v = v * hb := by decide +kernel
      obtain ⟨u, rfl⟩ := f.surjective v
      rw [← map_mul, ← map_mul, hbv]
    let q := hDecode (f hx) (f hb) (f hw)
    have himages : word hBasis q hx = f hx ∧ word hBasis q hb = f hb ∧
        word hBasis q hw = f hw := by
      simpa [hu, hw', hc, hb₁, hb₂, hcentral hx, hcentral hw, q, and_assoc] using
        h (f hx) (f hb) (f hw)
    exact ⟨q, hAut_ext himages.1 himages.2.1 himages.2.2⟩

private noncomputable def autEquiv : MulAut G ≃* MulAut H := by
  let eG := Equiv.ofBijective (word gBasis) gWord_bijective
  let eH := Equiv.ofBijective (word hBasis) hWord_bijective
  refine { eG.symm.trans eH with map_mul' := ?_ }
  intro f g
  obtain ⟨q, rfl⟩ := eG.surjective f
  obtain ⟨p, rfl⟩ := eG.surjective g
  change eH (eG.symm (word gBasis q * word gBasis p)) =
    eH (eG.symm (eG q)) * eH (eG.symm (eG p))
  rw [← word_mulCode gBasis gStep]
  change eH (eG.symm (eG (mulCode q p))) = _
  simpa only [Equiv.symm_apply_apply, eH, Equiv.coe_ofBijective] using
    word_mulCode hBasis hStep q p

/--
**A p-group and a proper subgroup with isomorphic automorphism groups (Kourovka 15.27).** For some
prime $p$ there are a finite $p$-group $G$ of order greater than $2$ and a proper subgroup $H < G$
with $\mathrm{Aut}(G) \cong \mathrm{Aut}(H)$ as groups.

T. Li's example is a $2$-group $G$ of order $32$ with a subgroup $H$ of order $16$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.27 (Ya. G.
Berkovich); resolution: T. Li, Arch. Math. 92 (2009), 287-290, Kourovka Archive, Problem 15.27
(answer: Yes, it is possible, for |G| = 2|H| = 32).
-/
public theorem autIsoAutOfProperSubgroup_holds : autIsoAutOfProperSubgroup := by
  have hcard : Nat.card G = 32 := by
    rw [SemidirectProduct.card]
    simp [V, C]
  refine ⟨2, Nat.prime_two, G, inferInstance, inferInstance,
    IsPGroup.of_card (n := 5) hcard, by omega, embed.range, ?_, ?_⟩
  · intro h
    have hmem : gy ∈ embed.range := h ▸ Subgroup.mem_top gy
    obtain ⟨v, hv⟩ := hmem
    have hn : ∀ t : C 2, double t ≠ gy.right := by decide +kernel
    exact hn v.right (congrArg (fun x : G ↦ x.right) hv)
  · exact ⟨autEquiv.trans (MulAut.congr (MonoidHom.ofInjective embed_injective))⟩

end MathlibExt.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27Wanted
