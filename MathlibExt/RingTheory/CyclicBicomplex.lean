/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/RingTheory/CyclicCohomology/Bicomplex.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import MathlibExt.RingTheory.CyclicCohomology
public import MathlibExt.RingTheory.CyclicRowExactness
public import Mathlib.Algebra.Homology.QuasiIso
import MathlibExt.Algebra.Homology.CyclicModuleHomology

/-!
# The total complex of the cyclic bicomplex

For an `R`-algebra `A` and an `R`-module `M`, write `C^q` for the `M`-valued multilinear maps in
`q + 1` arguments on `A`. Connes' cyclic bicomplex has the module `C^q` in every column `p` of
row `q`. Its horizontal differentials `C^q → C^q` alternate between `1 - λ` (out of even columns)
and the cyclic norm `N` (out of odd columns). Its vertical differentials `C^q → C^(q+1)` alternate
between the Hochschild coboundary `b` (in even columns) and `-b'` (in odd columns), where `b'` is
the bar coboundary. The relations `(1 - λ) b = b' (1 - λ)` and `b N = N b'` make adjacent squares
anticommute, so the sum of the two differentials squares to zero on the total complex.

The degree-`m` term of the total complex is `⊕_{p + q = m} C^q`. Here it is the submodule
`cyclicTotalCochains R A M m` of families `(x_q)_{q ∈ ℕ}` with `x_q ∈ C^q` and `x_q = 0` for
`q > m`; the component `x_q` sits in column `m - q`. Indexing by rows avoids natural-number
subtraction in the types of the components.

Column zero is the Hochschild cochain complex, and the kernel of its outgoing horizontal map
`1 - λ` is the module of cyclic cochains. Hence including a cyclic cochain into column zero gives a
cochain map `cyclicCochainComplexToTotal R A M` from Connes' cyclic cochain complex to the total
complex. When `q + 1` is invertible in `R`, the rows of the bicomplex are exact away from column
zero (`TauCeti.RingTheory.CyclicCohomology.RowExactness`), and this cochain map is a
quasi-isomorphism. So over a ring containing `ℚ`, cyclic cohomology defined by cyclic cochains is
the cohomology of the total cyclic bicomplex.

The total cochain modules require only additive commutative monoids of coefficients. Constructing
the total differential and its compatibility with cyclic cochains uses bilinear multiplication on
`A`; associativity is needed for the total differential to square to zero.

## Main definitions

* `TauCeti.cyclicBicomplexHorizontal`: the horizontal differential out of column `p` of row `q`.
* `TauCeti.cyclicBicomplexVertical`: the vertical differential in column `p` out of row `q`.
* `TauCeti.cyclicTotalCochains`: the degree-`m` term of the total complex.
* `TauCeti.cyclicTotalDifferential`: the total differential.
* `TauCeti.cyclicTotalComplex`: the total complex, a cochain complex of `R`-modules.
* `TauCeti.cyclicCochainsToTotal`, `TauCeti.cyclicCochainComplexToTotal`: the inclusion of cyclic
  cochains into column zero, and the resulting cochain map.
* `TauCeti.cyclicTotalHomologyMk`: the class of a total cocycle in the cohomology of the total
  complex.

## Main results

* `TauCeti.range_cyclicBicomplexHorizontal_eq_ker_cyclicBicomplexHorizontal`: the rows are exact
  away from column zero.
* `TauCeti.cyclicBicomplexVertical_comp_cyclicBicomplexHorizontal`: adjacent squares of the
  bicomplex anticommute.
* `TauCeti.cyclicTotalDifferential_cyclicTotalDifferential`: the total differential squares to
  zero.
* `TauCeti.quasiIsoAt_cyclicCochainComplexToTotal`: in degree `m`, the inclusion of the cyclic
  cochain complex is a quasi-isomorphism when `q + 1` is invertible for every `q < m`.
* `TauCeti.quasiIso_cyclicCochainComplexToTotal`: over a ring containing `ℚ`, the inclusion is a
  quasi-isomorphism.
* `TauCeti.homologyMap_cyclicCochainComplexToTotal_mk`: the inclusion sends the class of a cyclic
  cocycle to the class of the same cochain in column zero.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§2.1, 2.4.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

/-! ### The differentials of the cyclic bicomplex -/

section Horizontal

variable (R A M : Type*) [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M]

/-- The horizontal differential of the cyclic bicomplex out of column `p` in row `q`: `1 - λ`
out of an even column and the cyclic norm `N` out of an odd column. -/
def cyclicBicomplexHorizontal (p q : ℕ) :
    Module.End R (MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :=
  if Even p then 1 - cyclicOperator R A M q else cyclicNorm R A M q

variable {R A M} {p q : ℕ}

/-- Out of an even column the horizontal differential is `1 - λ`. -/
@[simp]
theorem cyclicBicomplexHorizontal_of_even (hp : Even p) :
    cyclicBicomplexHorizontal R A M p q = 1 - cyclicOperator R A M q :=
  ite_eq_left hp

/-- Out of an odd column the horizontal differential is the cyclic norm `N`. -/
@[simp]
theorem cyclicBicomplexHorizontal_of_odd (hp : Odd p) :
    cyclicBicomplexHorizontal R A M p q = cyclicNorm R A M q :=
  ite_eq_right (Nat.not_even_iff_odd.2 hp)

variable (R A M p q) in
/-- The horizontal differentials are periodic of period two in the column. -/
@[simp]
theorem cyclicBicomplexHorizontal_add_two :
    cyclicBicomplexHorizontal R A M (p + 2) q = cyclicBicomplexHorizontal R A M p q := by
  simp [cyclicBicomplexHorizontal, Nat.even_add]

/-- Two consecutive horizontal differentials compose to zero: `N (1 - λ) = 0 = (1 - λ) N`. -/
@[simp]
theorem cyclicBicomplexHorizontal_succ_mul_cyclicBicomplexHorizontal :
    cyclicBicomplexHorizontal R A M (p + 1) q * cyclicBicomplexHorizontal R A M p q = 0 := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexHorizontal_of_odd hp.add_one, cyclicBicomplexHorizontal_of_even hp,
      mul_sub, mul_one, cyclicNorm_mul_cyclicOperator, sub_self]
  · rw [cyclicBicomplexHorizontal_of_even hp.add_one, cyclicBicomplexHorizontal_of_odd hp,
      sub_mul, one_mul, cyclicOperator_mul_cyclicNorm, sub_self]

/-- Two consecutive horizontal differentials compose to zero, on elements. -/
@[simp]
theorem cyclicBicomplexHorizontal_cyclicBicomplexHorizontal
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    cyclicBicomplexHorizontal R A M (p + 1) q (cyclicBicomplexHorizontal R A M p q φ) = 0 := by
  rw [← Module.End.mul_apply, cyclicBicomplexHorizontal_succ_mul_cyclicBicomplexHorizontal,
    LinearMap.zero_apply]

variable (R A M p q) in
/-- When `q + 1` is invertible, the rows of the cyclic bicomplex are exact away from column zero:
the image of the horizontal differential into column `p + 1` is the kernel of the one out of it. -/
theorem range_cyclicBicomplexHorizontal_eq_ker_cyclicBicomplexHorizontal
    [Invertible (q + 1 : R)] :
    LinearMap.range (cyclicBicomplexHorizontal R A M p q) =
      LinearMap.ker (cyclicBicomplexHorizontal R A M (p + 1) q) := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexHorizontal_of_even hp, cyclicBicomplexHorizontal_of_odd hp.add_one,
      range_one_sub_cyclicOperator_eq_ker_cyclicNorm]
  · rw [cyclicBicomplexHorizontal_of_odd hp, cyclicBicomplexHorizontal_of_even hp.add_one,
      range_cyclicNorm_eq_ker_one_sub_cyclicOperator]

end Horizontal

section Vertical

variable (R A M : Type*) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The vertical differential of the cyclic bicomplex in column `p` out of row `q`: the
Hochschild coboundary `b` in an even column and minus the bar coboundary, `-b'`, in an odd
column. -/
def cyclicBicomplexVertical (p q : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (q + 2) ↦ A) M :=
  if Even p then hochschildCoboundary R A M q else -barCoboundary R A M q

variable {R A M} {p q : ℕ}

/-- In an even column the vertical differential is the Hochschild coboundary `b`. -/
@[simp]
theorem cyclicBicomplexVertical_of_even (hp : Even p) :
    cyclicBicomplexVertical R A M p q = hochschildCoboundary R A M q :=
  ite_eq_left hp

/-- In an odd column the vertical differential is `-b'`. -/
@[simp]
theorem cyclicBicomplexVertical_of_odd (hp : Odd p) :
    cyclicBicomplexVertical R A M p q = -barCoboundary R A M q :=
  ite_eq_right (Nat.not_even_iff_odd.2 hp)

variable (R A M p q) in
/-- The vertical differentials are periodic of period two in the column. -/
@[simp]
theorem cyclicBicomplexVertical_add_two :
    cyclicBicomplexVertical R A M (p + 2) q = cyclicBicomplexVertical R A M p q := by
  simp [cyclicBicomplexVertical, Nat.even_add]

variable (R A M p q) in
/-- Adjacent squares of the cyclic bicomplex anticommute: going right then up is minus going up
then right. In even columns this is `(1 - λ) b = b' (1 - λ)`, in odd columns `b N = N b'`. -/
theorem cyclicBicomplexVertical_comp_cyclicBicomplexHorizontal :
    cyclicBicomplexVertical R A M (p + 1) q ∘ₗ cyclicBicomplexHorizontal R A M p q =
      -(cyclicBicomplexHorizontal R A M p (q + 1) ∘ₗ cyclicBicomplexVertical R A M p q) := by
  rcases Nat.even_or_odd p with hp | hp
  · rw [cyclicBicomplexHorizontal_of_even hp, cyclicBicomplexVertical_of_even hp,
      cyclicBicomplexVertical_of_odd hp.add_one, cyclicBicomplexHorizontal_of_even hp,
      one_sub_cyclicOperator_comp_hochschildCoboundary, LinearMap.neg_comp]
  · rw [cyclicBicomplexHorizontal_of_odd hp, cyclicBicomplexVertical_of_odd hp,
      cyclicBicomplexVertical_of_even hp.add_one, cyclicBicomplexHorizontal_of_odd hp,
      LinearMap.comp_neg, hochschildCoboundary_comp_cyclicNorm, neg_neg]

/-- Adjacent squares of the cyclic bicomplex anticommute, on elements. -/
theorem cyclicBicomplexVertical_cyclicBicomplexHorizontal
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    cyclicBicomplexVertical R A M (p + 1) q (cyclicBicomplexHorizontal R A M p q φ) =
      -cyclicBicomplexHorizontal R A M p (q + 1) (cyclicBicomplexVertical R A M p q φ) :=
  LinearMap.congr_fun (cyclicBicomplexVertical_comp_cyclicBicomplexHorizontal R A M p q) φ

end Vertical

section VerticalAssoc

variable {R A M : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] {p q : ℕ}

/-- Two consecutive vertical differentials compose to zero: `b ∘ b = 0` and `b' ∘ b' = 0`. -/
@[simp]
theorem cyclicBicomplexVertical_cyclicBicomplexVertical
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :
    cyclicBicomplexVertical R A M p (q + 1) (cyclicBicomplexVertical R A M p q φ) = 0 := by
  rcases Nat.even_or_odd p with hp | hp
  · simp [hp]
  · simp [hp]

variable (R A M p q) in
/-- Two consecutive vertical differentials compose to zero, as a composite of linear maps. -/
theorem cyclicBicomplexVertical_comp_cyclicBicomplexVertical :
    cyclicBicomplexVertical R A M p (q + 1) ∘ₗ cyclicBicomplexVertical R A M p q = 0 :=
  LinearMap.ext cyclicBicomplexVertical_cyclicBicomplexVertical

end VerticalAssoc

/-! ### The total complex -/

section TotalCochains

variable (R A M : Type*) [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M]

/-- The degree-`m` term `⊕_{p + q = m} C^q` of the total complex of the cyclic bicomplex: the
families `(x_q)_q` of `M`-valued `q`-cochains with `x_q = 0` for `q > m`. The component `x_q` lies
in column `m - q`. -/
def cyclicTotalCochains (m : ℕ) :
    Submodule R (∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) :=
  Submodule.pi {q | m < q} fun _ ↦ ⊥

variable {R A M}

/-- A family of cochains lies in total degree `m` exactly when it vanishes above row `m`. -/
@[simp]
theorem mem_cyclicTotalCochains_iff {m : ℕ}
    {x : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M} :
    x ∈ cyclicTotalCochains R A M m ↔ ∀ q, m < q → x q = 0 := by
  simp [cyclicTotalCochains, Submodule.mem_pi]

/-- A total cochain of degree `m` vanishes in every row `q > m`. -/
@[simp]
theorem coe_cyclicTotalCochains_apply_of_lt {m q : ℕ} (x : cyclicTotalCochains R A M m)
    (hq : m < q) : (x : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) q = 0 :=
  mem_cyclicTotalCochains_iff.1 x.2 q hq

/-- A cochain placed in row `k ≤ m` is a total cochain of degree `m`. -/
theorem single_mem_cyclicTotalCochains {m k : ℕ} (hk : k ≤ m)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M) :
    (Pi.single k φ : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M) ∈
      cyclicTotalCochains R A M m := by
  rw [mem_cyclicTotalCochains_iff]
  intro q hq
  exact Pi.single_eq_of_ne (by omega) _

/-- A total cochain of degree `m` is a total cochain of every degree `n ≥ m`. -/
theorem cyclicTotalCochains_mono : Monotone (cyclicTotalCochains R A M) := fun m n hmn x hx ↦ by
  rw [mem_cyclicTotalCochains_iff] at hx ⊢
  exact fun q hq ↦ hx q (lt_of_le_of_lt hmn hq)

/-- A total cochain of degree `m` vanishing below row `m` is concentrated in column zero. -/
private theorem eq_single_of_forall_lt {m : ℕ}
    {x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M}
    (hx : x ∈ cyclicTotalCochains R A M m) (hlt : ∀ q < m, x q = 0) :
    x = (Pi.single m (x m) : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A)
        M) := by
  funext q
  rcases lt_trichotomy q m with hq | rfl | hq
  · rw [hlt q hq, Pi.single_eq_of_ne hq.ne]
  · rw [Pi.single_eq_same]
  · rw [mem_cyclicTotalCochains_iff.1 hx q hq, Pi.single_eq_of_ne hq.ne']

end TotalCochains

section Inclusion

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M]

variable (R A M) in
/-- The inclusion of cyclic `m`-cochains into column zero of the total complex. -/
def cyclicCochainsToTotal (m : ℕ) : cyclicCochains R A M m →ₗ[R] cyclicTotalCochains R A M m :=
  LinearMap.codRestrict _ ((LinearMap.single R _ m).comp (cyclicCochains R A M m).subtype)
    fun φ ↦ single_mem_cyclicTotalCochains le_rfl φ.1

/-- A cyclic cochain is included as the family concentrated in row `m`, column zero. -/
@[simp]
theorem coe_cyclicCochainsToTotal_apply {m : ℕ} (φ : cyclicCochains R A M m) :
    (cyclicCochainsToTotal R A M m φ : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1)
        ↦ A) M) =
      Pi.single m φ.1 :=
  (rfl)

variable (R A M) in
/-- The inclusion of cyclic cochains into column zero is injective. -/
theorem cyclicCochainsToTotal_injective (m : ℕ) :
    Function.Injective (cyclicCochainsToTotal R A M m) := fun _ _ h ↦
  Subtype.ext (Pi.single_injective m (congrArg Subtype.val h))

end Inclusion

section Total

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (R A M) in
/-- The components of the total differential on families of cochains: row `0` receives the
horizontal differential out of column `m`, and row `q + 1` receives the vertical differential of
the component in row `q` and the horizontal differential of the component in row `q + 1`. -/
private def cyclicTotalDifferentialComponent (m : ℕ) :
    ∀ q : ℕ, (∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M) →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A) M
  | 0 => cyclicBicomplexHorizontal R A M m 0 ∘ₗ LinearMap.proj 0
  | q + 1 => cyclicBicomplexVertical R A M (m - q) q ∘ₗ LinearMap.proj q +
      cyclicBicomplexHorizontal R A M (m - (q + 1)) (q + 1) ∘ₗ LinearMap.proj (q + 1)

variable (R A M) in
/-- The total differential on all families of cochains, with the components of degree `m` placed
in the columns `m - q`. -/
private def cyclicTotalDifferentialAux (m : ℕ) :
    (∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M) →ₗ[R]
      ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M :=
  LinearMap.pi (cyclicTotalDifferentialComponent R A M m)

private theorem cyclicTotalDifferentialAux_apply_zero (m : ℕ)
    (x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M) :
    cyclicTotalDifferentialAux R A M m x 0 = cyclicBicomplexHorizontal R A M m 0 (x 0) :=
  (rfl)

private theorem cyclicTotalDifferentialAux_apply_succ (m q : ℕ)
    (x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M) :
    cyclicTotalDifferentialAux R A M m x (q + 1) =
      cyclicBicomplexVertical R A M (m - q) q (x q) +
        cyclicBicomplexHorizontal R A M (m - (q + 1)) (q + 1) (x (q + 1)) :=
  (rfl)

/-- If a family vanishes below row `k`, its total differential in row `k` is the horizontal
differential of its component in row `k`. -/
private theorem cyclicTotalDifferentialAux_apply_of_forall_lt (m k : ℕ)
    (x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M) (hx : ∀ q < k, x q =
        0) :
    cyclicTotalDifferentialAux R A M m x k = cyclicBicomplexHorizontal R A M (m - k) k (x k) := by
  cases k with
  | zero => rw [cyclicTotalDifferentialAux_apply_zero, Nat.sub_zero]
  | succ k => rw [cyclicTotalDifferentialAux_apply_succ, hx k k.lt_add_one, map_zero, zero_add]

/-- The total differential of a cochain placed in row `k` vanishes below row `k`. -/
private theorem cyclicTotalDifferentialAux_single_apply_of_lt (m : ℕ) {k q : ℕ} (hq : q < k)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M) :
    cyclicTotalDifferentialAux R A M m (Pi.single k φ) q = 0 := by
  cases q with
  | zero => rw [cyclicTotalDifferentialAux_apply_zero, Pi.single_eq_of_ne hq.ne, map_zero]
  | succ q =>
    rw [cyclicTotalDifferentialAux_apply_succ, Pi.single_eq_of_ne (by omega),
      Pi.single_eq_of_ne hq.ne, map_zero, map_zero, add_zero]

/-- The total differential maps total degree `m` to total degree `m + 1`. -/
private theorem cyclicTotalDifferentialAux_mem {m : ℕ}
    {x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M}
    (hx : x ∈ cyclicTotalCochains R A M m) :
    cyclicTotalDifferentialAux R A M m x ∈ cyclicTotalCochains R A M (m + 1) := by
  rw [mem_cyclicTotalCochains_iff] at hx ⊢
  intro q hq
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.zero_lt_of_lt hq)
  rw [zero_add, cyclicTotalDifferentialAux_apply_succ, hx q (by omega), hx (q + 1) (by omega),
    map_zero, map_zero, add_zero]

variable (R A M) in
/-- The differential `D = d_h + d_v` of the total complex of the cyclic bicomplex, from total
degree `m` to total degree `m + 1`. -/
def cyclicTotalDifferential (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R A M (m + 1) :=
  (cyclicTotalDifferentialAux R A M m).restrict fun _ ↦ cyclicTotalDifferentialAux_mem

private theorem coe_cyclicTotalDifferential {m : ℕ} (x : cyclicTotalCochains R A M m) :
    (cyclicTotalDifferential R A M m x).1 = cyclicTotalDifferentialAux R A M m x.1 :=
  (rfl)

/-- In row zero, the total differential is the horizontal differential out of column `m`. -/
@[simp]
theorem cyclicTotalDifferential_apply_zero {m : ℕ} (x : cyclicTotalCochains R A M m) :
    (cyclicTotalDifferential R A M m x).1 0 = cyclicBicomplexHorizontal R A M m 0 (x.1 0) :=
  (rfl)

/-- In row `q + 1`, the total differential adds the vertical differential of the component in
row `q`, in column `m - q`, to the horizontal differential of the component in row `q + 1`. -/
@[simp]
theorem cyclicTotalDifferential_apply_succ {m : ℕ} (x : cyclicTotalCochains R A M m) (q : ℕ) :
    (cyclicTotalDifferential R A M m x).1 (q + 1) =
      cyclicBicomplexVertical R A M (m - q) q (x.1 q) +
        cyclicBicomplexHorizontal R A M (m - (q + 1)) (q + 1) (x.1 (q + 1)) :=
  (rfl)

/-- The total differential of a cochain `φ` in column zero of row `m` has the components
`(1 - λ) φ` in row `m` and `b φ` in row `m + 1`. -/
private theorem cyclicTotalDifferentialAux_single_self (m : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ A) M) :
    cyclicTotalDifferentialAux R A M m (Pi.single m φ) m = (1 - cyclicOperator R A M m) φ ∧
      cyclicTotalDifferentialAux R A M m (Pi.single m φ) (m + 1) =
        hochschildCoboundary R A M m φ := by
  refine ⟨?_, ?_⟩
  · rw [cyclicTotalDifferentialAux_apply_of_forall_lt m m _ fun q hq ↦ Pi.single_eq_of_ne hq.ne _,
      Nat.sub_self, Pi.single_eq_same, cyclicBicomplexHorizontal_of_even Even.zero]
  · rw [cyclicTotalDifferentialAux_apply_succ, Nat.sub_self, Pi.single_eq_same,
      Pi.single_eq_of_ne (by omega), map_zero, add_zero,
      cyclicBicomplexVertical_of_even Even.zero]

/-- The inclusion into column zero commutes with the differentials: the total differential of a
cyclic cochain `φ` is `(1 - λ) φ = 0` in column one plus `b φ` in column zero. -/
@[simp]
theorem cyclicTotalDifferential_cyclicCochainsToTotal {m : ℕ} (φ : cyclicCochains R A M m) :
    cyclicTotalDifferential R A M m (cyclicCochainsToTotal R A M m φ) =
      cyclicCochainsToTotal R A M (m + 1) (cyclicHochschildCoboundary R A M m φ) := by
  obtain ⟨hcyc, hb⟩ := cyclicTotalDifferentialAux_single_self m φ.1
  have hφ : (1 - cyclicOperator R A M m) φ.1 = 0 := by
    rw [← LinearMap.mem_ker, ker_one_sub_cyclicOperator]
    exact φ.2
  apply Subtype.ext
  rw [coe_cyclicTotalDifferential, coe_cyclicCochainsToTotal_apply, coe_cyclicCochainsToTotal_apply,
    coe_cyclicHochschildCoboundary_apply,
    eq_single_of_forall_lt
      (cyclicTotalDifferentialAux_mem (single_mem_cyclicTotalCochains le_rfl _))
      fun q hq ↦ ?_, hb]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
  · exact cyclicTotalDifferentialAux_single_apply_of_lt m hq φ.1
  · rw [hcyc, hφ]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- In row `q + 1` of a total cochain `x` of degree `m`, the horizontal differential out of the
column `m - (q + 1)` of `x (q + 1)`, followed by the one out of the column `m - q`, vanishes. -/
private theorem cyclicBicomplexHorizontal_cyclicBicomplexHorizontal_of_mem {m : ℕ}
    {x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M}
    (hx : x ∈ cyclicTotalCochains R A M m) (q : ℕ) :
    cyclicBicomplexHorizontal R A M (m - q) (q + 1)
      (cyclicBicomplexHorizontal R A M (m - (q + 1)) (q + 1) (x (q + 1))) = 0 := by
  -- Below row `m + 1`, the column `m - (q + 1)` precedes the column `m - q`.
  rcases lt_or_ge q m with hq | hq
  · rw [show m - q = m - (q + 1) + 1 by omega, cyclicBicomplexHorizontal_cyclicBicomplexHorizontal]
  · rw [mem_cyclicTotalCochains_iff.1 hx (q + 1) (by omega), map_zero, map_zero]

/-- In row `q + 1` of a total cochain `x` of degree `m`, the square leaving `x (q + 1)` in the
column `m - (q + 1)` anticommutes. -/
private theorem cyclicBicomplexVertical_cyclicBicomplexHorizontal_of_mem {m : ℕ}
    {x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M}
    (hx : x ∈ cyclicTotalCochains R A M m) (q : ℕ) :
    cyclicBicomplexVertical R A M (m - q) (q + 1)
        (cyclicBicomplexHorizontal R A M (m - (q + 1)) (q + 1) (x (q + 1))) =
      -cyclicBicomplexHorizontal R A M (m - (q + 1)) (q + 2)
        (cyclicBicomplexVertical R A M (m - (q + 1)) (q + 1) (x (q + 1))) := by
  -- Below row `m + 1`, the column `m - (q + 1)` precedes the column `m - q`.
  rcases lt_or_ge q m with hq | hq
  · rw [show m - q = m - (q + 1) + 1 by omega, cyclicBicomplexVertical_cyclicBicomplexHorizontal]
  · rw [mem_cyclicTotalCochains_iff.1 hx (q + 1) (by omega), map_zero, map_zero, map_zero,
      map_zero, neg_zero]

end Total

section TotalAssoc

variable {R A M : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The total differential squares to zero on total cochains of degree `m`. -/
private theorem cyclicTotalDifferentialAux_cyclicTotalDifferentialAux {m : ℕ}
    {x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M}
    (hx : x ∈ cyclicTotalCochains R A M m) :
    cyclicTotalDifferentialAux R A M (m + 1) (cyclicTotalDifferentialAux R A M m x) = 0 := by
  funext q
  cases q with
  | zero =>
    rw [cyclicTotalDifferentialAux_apply_zero, cyclicTotalDifferentialAux_apply_zero,
      cyclicBicomplexHorizontal_cyclicBicomplexHorizontal, Pi.zero_apply]
  | succ q =>
    rw [cyclicTotalDifferentialAux_apply_succ, cyclicTotalDifferentialAux_apply_succ,
      Nat.add_sub_add_right, map_add, cyclicBicomplexHorizontal_cyclicBicomplexHorizontal_of_mem hx,
      add_zero, Pi.zero_apply]
    cases q with
    | zero =>
      rw [cyclicTotalDifferentialAux_apply_zero, Nat.sub_zero, Nat.sub_zero,
        cyclicBicomplexVertical_cyclicBicomplexHorizontal]
      exact neg_add_cancel _
    | succ q =>
      rw [cyclicTotalDifferentialAux_apply_succ, Nat.add_sub_add_right, map_add,
        cyclicBicomplexVertical_cyclicBicomplexVertical, zero_add,
        cyclicBicomplexVertical_cyclicBicomplexHorizontal_of_mem hx, neg_add_cancel]

/-- The total differential squares to zero. -/
@[simp]
theorem cyclicTotalDifferential_cyclicTotalDifferential {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R A M (m + 1) (cyclicTotalDifferential R A M m x) = 0 :=
  Subtype.ext (cyclicTotalDifferentialAux_cyclicTotalDifferentialAux x.2)

variable (R A M) in
/-- The total differential squares to zero, as a composite of linear maps. -/
theorem cyclicTotalDifferential_comp_cyclicTotalDifferential (m : ℕ) :
    cyclicTotalDifferential R A M (m + 1) ∘ₗ cyclicTotalDifferential R A M m = 0 :=
  LinearMap.ext cyclicTotalDifferential_cyclicTotalDifferential

end TotalAssoc

section Reduction

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- **Killing one column.** Let `x` be a family of cochains whose total differential vanishes in
row `k ≤ m`, and let `y` be a total cochain of degree `m` whose total differential agrees with `x`
in the rows `q < k`. If `k + 1` is invertible, adding a suitable cochain in row `k` to `y` makes
them agree in the rows `q ≤ k`, by exactness of row `k` away from column zero. -/
private theorem exists_forall_lt_succ_eq_cyclicTotalDifferentialAux {m k : ℕ} (hk : k ≤ m)
    (hR : IsUnit ((k : R) + 1)) {x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦
        A) M}
    (hdx : cyclicTotalDifferentialAux R A M (m + 1) x k = 0)
    {y : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M}
    (hy : y ∈ cyclicTotalCochains R A M m)
    (hxy : ∀ q < k, x q = cyclicTotalDifferentialAux R A M m y q) :
    ∃ y' ∈ cyclicTotalCochains R A M m,
      ∀ q < k + 1, x q = cyclicTotalDifferentialAux R A M m y' q := by
  -- the remainder `x - D y` vanishes below row `k` and has the same differential as `x`
  have hlt : ∀ q < k, (x - cyclicTotalDifferentialAux R A M m y) q = 0 := fun q hq ↦ by
    rw [Pi.sub_apply, hxy q hq, sub_self]
  rw [← sub_zero (cyclicTotalDifferentialAux R A M (m + 1) x),
    ← cyclicTotalDifferentialAux_cyclicTotalDifferentialAux hy, ← map_sub,
    cyclicTotalDifferentialAux_apply_of_forall_lt _ _ _ hlt,
    show m + 1 - k = m - k + 1 by omega] at hdx
  have := hR.invertible
  obtain ⟨z, hz⟩ : (x - cyclicTotalDifferentialAux R A M m y) k ∈
      LinearMap.range (cyclicBicomplexHorizontal R A M (m - k) k) := by
    rw [range_cyclicBicomplexHorizontal_eq_ker_cyclicBicomplexHorizontal]
    exact hdx
  refine ⟨y + Pi.single k z, add_mem hy (single_mem_cyclicTotalCochains hk z), fun q hq ↦ ?_⟩
  rw [map_add, Pi.add_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
  · rw [cyclicTotalDifferentialAux_single_apply_of_lt m hq, add_zero, hxy q hq]
  · rw [cyclicTotalDifferentialAux_apply_of_forall_lt m q (Pi.single q z)
      fun q' hq' ↦ Pi.single_eq_of_ne hq'.ne _, Pi.single_eq_same, hz, Pi.sub_apply,
      add_sub_cancel]

/-- **Killing the columns of a total cochain.** Let `x` be a total cochain of degree `m + 1` whose
total differential vanishes below row `m + 1`. If `q + 1` is invertible for `q ≤ m`, then `x` is
the sum of a cochain in column zero and the total differential of a total cochain of degree `m`. -/
private theorem exists_eq_single_add_cyclicTotalDifferentialAux {m : ℕ}
    (hR : ∀ q ≤ m, IsUnit ((q : R) + 1))
    {x : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M}
    (hx : x ∈ cyclicTotalCochains R A M (m + 1))
    (hdx : ∀ q ≤ m, cyclicTotalDifferentialAux R A M (m + 1) x q = 0) :
    ∃ y ∈ cyclicTotalCochains R A M m, ∃ φ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦
        A) M,
      x = (Pi.single (m + 1) φ : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1) ↦ A)
          M) +
        cyclicTotalDifferentialAux R A M m y := by
  -- Kill the components in the rows `q < k`, by induction on `k`, using exactness of the rows
  -- away from column zero.
  have key (k : ℕ) (hk : k ≤ m + 1) : ∃ y ∈ cyclicTotalCochains R A M m,
      ∀ q < k, x q = cyclicTotalDifferentialAux R A M m y q := by
    induction k with
    | zero => exact ⟨0, zero_mem _, fun q hq ↦ absurd hq (Nat.not_lt_zero q)⟩
    | succ k ih =>
      obtain ⟨y, hy, hxy⟩ := ih (by omega)
      exact exists_forall_lt_succ_eq_cyclicTotalDifferentialAux (by omega) (hR k (by omega))
        (hdx k (by omega)) hy hxy
  -- The remainder vanishes below row `m + 1`, so it is concentrated in column zero.
  obtain ⟨y, hy, hxy⟩ := key (m + 1) le_rfl
  refine ⟨y, hy, (x - cyclicTotalDifferentialAux R A M m y) (m + 1), ?_⟩
  rw [← eq_single_of_forall_lt (sub_mem hx (cyclicTotalDifferentialAux_mem hy))
    fun q hq ↦ by rw [Pi.sub_apply, hxy q hq, sub_self], sub_add_cancel]

/-- If the total differential of a total cochain `y` of degree `m` is a cochain `φ` in column
zero of row `m + 1`, and `q + 1` is invertible for `q < m`, then `φ` is the Hochschild
coboundary of a cyclic cochain. -/
private theorem exists_hochschildCoboundary_eq_of_cyclicTotalDifferentialAux_eq_single {m : ℕ}
    (hR : ∀ q < m, IsUnit ((q : R) + 1))
    {y : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (k + 1) ↦ A) M}
    (hy : y ∈ cyclicTotalCochains R A M m) {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2)
        ↦ A) M}
    (hyφ : cyclicTotalDifferentialAux R A M m y = Pi.single (m + 1) φ) :
    ∃ ψ ∈ cyclicCochains R A M m, hochschildCoboundary R A M m ψ = φ := by
  -- Replace `y` by a cochain `Pi.single m ψ` in column zero with the same differential.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ A) M,
      cyclicTotalDifferentialAux R A M m (Pi.single m ψ) = Pi.single (m + 1) φ := by
    cases m with
    | zero =>
      exact ⟨y 0, by rwa [← eq_single_of_forall_lt hy fun q hq ↦ absurd hq (Nat.not_lt_zero q)]⟩
    | succ m =>
      obtain ⟨u, hu, ψ, rfl⟩ := exists_eq_single_add_cyclicTotalDifferentialAux
        (fun q hq ↦ hR q (by omega)) hy fun q hq ↦ by
          rw [hyφ, Pi.single_eq_of_ne (by omega)]
      refine ⟨ψ, ?_⟩
      rwa [map_add, cyclicTotalDifferentialAux_cyclicTotalDifferentialAux hu, add_zero] at hyφ
  obtain ⟨hcyc, hb⟩ := cyclicTotalDifferentialAux_single_self m ψ
  rw [hψ, Pi.single_eq_of_ne (Nat.lt_succ_self m).ne] at hcyc
  rw [hψ, Pi.single_eq_same] at hb
  exact ⟨ψ, by rw [← ker_one_sub_cyclicOperator]; exact hcyc.symm, hb.symm⟩

end Reduction

/-! ### The total complex and the comparison with cyclic cochains -/

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The total complex of Connes' cyclic bicomplex, a cochain complex of `R`-modules indexed by
`ℕ`. -/
def cyclicTotalComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun m ↦ ModuleCat.of R (cyclicTotalCochains R A M m))
    (fun m ↦ ModuleCat.ofHom (cyclicTotalDifferential R A M m))
    fun m ↦ ModuleCat.hom_ext (cyclicTotalDifferential_comp_cyclicTotalDifferential R A M m)

/-- The degree-`m` term of the total complex is the module of total cochains of degree `m`. -/
def cyclicTotalComplexXIso (m : ℕ) :
    (cyclicTotalComplex R A M).X m ≅ ModuleCat.of R (cyclicTotalCochains R A M m) :=
  Iso.refl _

/-- Under the identifications `cyclicTotalComplexXIso`, the differential of the total complex is
the total differential. -/
@[reassoc, elementwise]
theorem cyclicTotalComplex_d (m : ℕ) :
    (cyclicTotalComplex R A M).d m (m + 1) ≫ (cyclicTotalComplexXIso R A M (m + 1)).hom =
      (cyclicTotalComplexXIso R A M m).hom ≫
        ModuleCat.ofHom (cyclicTotalDifferential R A M m) := by
  simp [cyclicTotalComplex, cyclicTotalComplexXIso]

/-- The cochain map from Connes' cyclic cochain complex to the total complex of the cyclic
bicomplex, including cyclic cochains into column zero. -/
def cyclicCochainComplexToTotal : cyclicCochainComplex R A M ⟶ cyclicTotalComplex R A M where
  f m := (cyclicCochainComplexXIso R A M m).hom ≫ ModuleCat.ofHom (cyclicCochainsToTotal R A M m) ≫
    (cyclicTotalComplexXIso R A M m).inv
  comm' := by
    rintro m _ rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
    apply (ModuleCat.mono_iff_injective (cyclicTotalComplexXIso R A M (m + 1)).hom).1
      inferInstance
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cyclicTotalComplex_d_apply,
      Iso.inv_hom_id_apply, cyclicCochainComplex_d_apply, ModuleCat.hom_ofHom]
    exact cyclicTotalDifferential_cyclicCochainsToTotal _

/-- Under the identifications of the terms of both complexes, the cochain map to the total complex
is the inclusion `cyclicCochainsToTotal` into column zero. -/
@[reassoc, elementwise]
theorem cyclicCochainComplexToTotal_f (m : ℕ) :
    (cyclicCochainComplexToTotal R A M).f m ≫ (cyclicTotalComplexXIso R A M m).hom =
      (cyclicCochainComplexXIso R A M m).hom ≫ ModuleCat.ofHom (cyclicCochainsToTotal R A M m) := by
  simp [cyclicCochainComplexToTotal]

variable {R A M} in
/-- A total cocycle of degree zero is a cyclic cochain in column zero. -/
private theorem exists_cyclicCochainsToTotal_eq_of_zero (x : cyclicTotalCochains R A M 0)
    (hx : cyclicTotalDifferential R A M 0 x = 0) :
    ∃ φ, cyclicCochainsToTotal R A M 0 φ = x := by
  have hx0 := eq_single_of_forall_lt x.2 fun q hq ↦ absurd hq (Nat.not_lt_zero q)
  have h := (cyclicTotalDifferentialAux_single_self 0 (x.1 0)).1
  rw [← hx0, ← coe_cyclicTotalDifferential, hx, Submodule.coe_zero, Pi.zero_apply] at h
  refine ⟨⟨x.1 0, ?_⟩, Subtype.ext ?_⟩
  · rw [← ker_one_sub_cyclicOperator]
    exact h.symm
  · rw [coe_cyclicCochainsToTotal_apply]
    exact hx0.symm

variable {R A M} in
/-- A total cocycle of degree `m + 1` is a cyclic cochain in column zero up to a total
coboundary, when `q + 1` is invertible for `q ≤ m`. -/
private theorem exists_cyclicCochainsToTotal_add_cyclicTotalDifferential_eq {m : ℕ}
    (hR : ∀ q ≤ m, IsUnit ((q : R) + 1)) (x : cyclicTotalCochains R A M (m + 1))
    (hx : cyclicTotalDifferential R A M (m + 1) x = 0) :
    ∃ φ y, cyclicCochainsToTotal R A M (m + 1) φ + cyclicTotalDifferential R A M m y = x := by
  have hx' : cyclicTotalDifferentialAux R A M (m + 1) x.1 = 0 := by
    rw [← coe_cyclicTotalDifferential, hx, Submodule.coe_zero]
  obtain ⟨y, hy, w, hw⟩ := exists_eq_single_add_cyclicTotalDifferentialAux hR x.2
    fun q _ ↦ by rw [hx', Pi.zero_apply]
  have h := (cyclicTotalDifferentialAux_single_self (m + 1) w).1
  rw [eq_sub_of_add_eq hw.symm, map_sub, hx',
    cyclicTotalDifferentialAux_cyclicTotalDifferentialAux hy, sub_zero, Pi.zero_apply] at h
  refine ⟨⟨w, ?_⟩, ⟨y, hy⟩, Subtype.ext ?_⟩
  · rw [← ker_one_sub_cyclicOperator]
    exact h.symm
  · rw [Submodule.coe_add, coe_cyclicCochainsToTotal_apply, coe_cyclicTotalDifferential]
    exact hw.symm

variable {R A M} in
/-- A cyclic cochain in column zero which is a total coboundary is the coboundary of a cyclic
cochain, when `q + 1` is invertible for `q < m`. -/
private theorem exists_cyclicHochschildCoboundary_eq {m : ℕ}
    (hR : ∀ q < m, IsUnit ((q : R) + 1)) (φ : cyclicCochains R A M (m + 1))
    (y : cyclicTotalCochains R A M m)
    (hy : cyclicTotalDifferential R A M m y = cyclicCochainsToTotal R A M (m + 1) φ) :
    ∃ ψ, cyclicHochschildCoboundary R A M m ψ = φ := by
  have hy' := congrArg Subtype.val hy
  rw [coe_cyclicTotalDifferential, coe_cyclicCochainsToTotal_apply] at hy'
  obtain ⟨ψ, hψ, hbψ⟩ :=
    exists_hochschildCoboundary_eq_of_cyclicTotalDifferentialAux_eq_single hR y.2 hy'
  exact ⟨⟨ψ, hψ⟩, Subtype.ext (by rw [coe_cyclicHochschildCoboundary_apply, hbψ])⟩

/-- The components of the cochain map into the total complex are injective. -/
private theorem cyclicCochainComplexToTotal_f_injective (n : ℕ) :
    Function.Injective ((cyclicCochainComplexToTotal R A M).f n) := fun φ ψ h ↦
  (ModuleCat.mono_iff_injective (cyclicCochainComplexXIso R A M n).hom).1 inferInstance <|
    cyclicCochainsToTotal_injective R A M n <| by
      rw [← cyclicCochainComplexToTotal_f_apply, ← cyclicCochainComplexToTotal_f_apply, h]

variable {R A M} in
/-- In degree `m`, a cyclic cochain whose image in the total complex is a total coboundary is a
cyclic coboundary, when `q + 1` is invertible for `q < m`. Here `p` is the degree preceding
`m`. -/
private theorem exists_cyclicCochainComplex_d_eq {m p : ℕ} (hp : (ComplexShape.up ℕ).prev m = p)
    (hR : ∀ q < m, IsUnit ((q : R) + 1)) (φ : (cyclicCochainComplex R A M).X m)
    (y : (cyclicTotalComplex R A M).X p)
    (hy : (cyclicTotalComplex R A M).d p m y = (cyclicCochainComplexToTotal R A M).f m φ) :
    ∃ ψ, (cyclicCochainComplex R A M).d p m ψ = φ := by
  cases m with
  | zero =>
    -- In degree zero there are no total coboundaries, so `φ = 0`.
    obtain rfl : p = 0 := hp.symm.trans CochainComplex.prev_nat_zero
    refine ⟨0, cyclicCochainComplexToTotal_f_injective R A M 0 ?_⟩
    rw [← hy, (cyclicTotalComplex R A M).shape 0 0 (by simp)]
    simp
  | succ m =>
    obtain rfl : m = p := (CochainComplex.prev_nat_succ m).symm.trans hp
    have hy' := congrArg (cyclicTotalComplexXIso R A M (m + 1)).hom hy
    rw [cyclicTotalComplex_d_apply, cyclicCochainComplexToTotal_f_apply] at hy'
    obtain ⟨ψ, hψ⟩ := exists_cyclicHochschildCoboundary_eq (fun q hq ↦ hR q (by omega)) _ _ hy'
    refine ⟨(cyclicCochainComplexXIso R A M m).inv ψ,
      (ModuleCat.mono_iff_injective (cyclicCochainComplexXIso R A M (m + 1)).hom).1
        inferInstance ?_⟩
    rw [cyclicCochainComplex_d_apply, Iso.inv_hom_id_apply, hψ]

variable {R A M} in
/-- In degree `m`, every total cocycle is the image of a cyclic cochain up to a total coboundary,
when `q + 1` is invertible for `q < m`. Here `p` is the degree preceding `m`. -/
private theorem exists_cyclicCochainComplexToTotal_f_add_cyclicTotalComplex_d_eq {m p : ℕ}
    (hp : (ComplexShape.up ℕ).prev m = p) (hR : ∀ q < m, IsUnit ((q : R) + 1))
    (x : (cyclicTotalComplex R A M).X m) (hx : (cyclicTotalComplex R A M).d m (m + 1) x = 0) :
    ∃ φ y, (cyclicCochainComplexToTotal R A M).f m φ + (cyclicTotalComplex R A M).d p m y = x := by
  have hL (n : ℕ) :=
    (ModuleCat.mono_iff_injective (cyclicTotalComplexXIso R A M n).hom).1 inferInstance
  have hx' : cyclicTotalDifferential R A M m ((cyclicTotalComplexXIso R A M m).hom x) = 0 := by
    rw [← cyclicTotalComplex_d_apply, hx, map_zero]
  cases m with
  | zero =>
    -- In degree zero a total cocycle is a cyclic cocycle in column zero.
    obtain rfl : p = 0 := hp.symm.trans CochainComplex.prev_nat_zero
    obtain ⟨φ, hφ⟩ := exists_cyclicCochainsToTotal_eq_of_zero _ hx'
    refine ⟨(cyclicCochainComplexXIso R A M 0).inv φ, 0, hL 0 ?_⟩
    rw [map_zero, add_zero, cyclicCochainComplexToTotal_f_apply, Iso.inv_hom_id_apply, hφ]
  | succ m =>
    -- In positive degree it is a cyclic cocycle in column zero up to a total coboundary.
    obtain rfl : m = p := (CochainComplex.prev_nat_succ m).symm.trans hp
    obtain ⟨φ, y, hφy⟩ := exists_cyclicCochainsToTotal_add_cyclicTotalDifferential_eq
      (fun q hq ↦ hR q (by omega)) _ hx'
    refine ⟨(cyclicCochainComplexXIso R A M (m + 1)).inv φ,
      (cyclicTotalComplexXIso R A M m).inv y, hL (m + 1) ?_⟩
    rw [map_add, cyclicCochainComplexToTotal_f_apply, cyclicTotalComplex_d_apply,
      Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, hφy]

/-- In degree `m`, a cyclic cocycle whose image is a total coboundary is a cyclic coboundary. -/
private theorem injective_homologyMap_cyclicCochainComplexToTotal (m : ℕ)
    (hR : ∀ q < m, IsUnit ((q : R) + 1)) :
    Function.Injective (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨φ, hφ, rfl⟩ := (cyclicCochainComplex R A M).exists_homologyπ_moduleCatCyclesMk_eq
    _ (CochainComplex.next ℕ m) c
  rw [HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk,
    HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _ rfl] at hc
  obtain ⟨y, hy⟩ := hc
  have hy' := congrArg ((cyclicTotalComplex R A M).iCycles m) hy
  rw [HomologicalComplex.moduleCat_iCycles_toCycles_apply,
    HomologicalComplex.iCycles_moduleCatCyclesMk] at hy'
  obtain ⟨ψ, hψ⟩ := exists_cyclicCochainComplex_d_eq rfl hR φ y hy'
  rw [HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _ rfl]
  refine ⟨ψ, (cyclicCochainComplex R A M).moduleCat_iCycles_injective m ?_⟩
  rw [HomologicalComplex.moduleCat_iCycles_toCycles_apply,
    HomologicalComplex.iCycles_moduleCatCyclesMk, hψ]

/-- In degree `m`, every total cocycle is the image of a cyclic cocycle up to a total coboundary. -/
private theorem surjective_homologyMap_cyclicCochainComplexToTotal (m : ℕ)
    (hR : ∀ q < m, IsUnit ((q : R) + 1)) :
    Function.Surjective (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m) := by
  intro c
  obtain ⟨x, hx, rfl⟩ := (cyclicTotalComplex R A M).exists_homologyπ_moduleCatCyclesMk_eq
    _ (CochainComplex.next ℕ m) c
  obtain ⟨φ, y, hφy⟩ :=
    exists_cyclicCochainComplexToTotal_f_add_cyclicTotalComplex_d_eq rfl hR x hx
  -- the cyclic cochain `φ` is a cocycle, since its image `x - d y` is a total cocycle
  have hφ : (cyclicCochainComplex R A M).d m (m + 1) φ = 0 :=
    cyclicCochainComplexToTotal_f_injective R A M (m + 1) (by
      rw [← HomologicalComplex.Hom.comm_apply, eq_sub_of_add_eq hφy, map_sub, hx,
        HomologicalComplex.d_comp_d_apply, sub_zero, map_zero])
  refine ⟨(cyclicCochainComplex R A M).homologyπ m
    ((cyclicCochainComplex R A M).moduleCatCyclesMk φ _ (CochainComplex.next ℕ m) hφ), ?_⟩
  rw [HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  refine ((cyclicTotalComplex R A M).moduleCat_homologyπ_eq_of_iCycles_sub_eq_d y ?_).symm
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk,
    HomologicalComplex.iCycles_moduleCatCyclesMk, ← hφy, add_sub_cancel_left]

/-- **Cyclic cochains compute the cohomology of the cyclic bicomplex.** In degree `m`, the
inclusion of Connes' cyclic cochain complex into column zero of the total complex of the cyclic
bicomplex is a quasi-isomorphism, provided `q + 1` is invertible in `R` for every `q < m`. -/
theorem quasiIsoAt_cyclicCochainComplexToTotal (m : ℕ) (hR : ∀ q < m, IsUnit ((q : R) + 1)) :
    QuasiIsoAt (cyclicCochainComplexToTotal R A M) m := by
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact ⟨injective_homologyMap_cyclicCochainComplexToTotal R A M m hR,
    surjective_homologyMap_cyclicCochainComplexToTotal R A M m hR⟩

/-- Over a ring containing `ℚ`, the inclusion of Connes' cyclic cochain complex into the total
complex of the cyclic bicomplex is a quasi-isomorphism: cyclic cohomology defined by cyclic cochains
is the cohomology of the total cyclic bicomplex. -/
theorem quasiIso_cyclicCochainComplexToTotal [Algebra ℚ R] :
    QuasiIso (cyclicCochainComplexToTotal R A M) := by
  rw [quasiIso_iff]
  refine fun m ↦ quasiIsoAt_cyclicCochainComplexToTotal R A M m fun q _ ↦ ?_
  simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R)

/-- Over a ring containing `ℚ`, the inclusion of cyclic cochains into column zero is bijective on
cohomology. -/
theorem bijective_homologyMap_cyclicCochainComplexToTotal [Algebra ℚ R] (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n) :=
  (ConcreteCategory.isIso_iff_bijective _).1 ((quasiIsoAt_iff_isIso_homologyMap _ _).1
    ((quasiIso_iff _).1 (quasiIso_cyclicCochainComplexToTotal R A M) n))

end Complex

/-! ### Total cohomology classes -/

section Classes

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- A total cochain is a total cocycle exactly when the differential of the total complex kills
it. -/
theorem mem_ker_cyclicTotalDifferential_iff (n : ℕ) (x : cyclicTotalCochains R A M n) :
    x ∈ LinearMap.ker (cyclicTotalDifferential R A M n) ↔
      (cyclicTotalComplex R A M).d n (n + 1) ((cyclicTotalComplexXIso R A M n).inv x) = 0 := by
  rw [LinearMap.mem_ker, (cyclicTotalComplex R A M).moduleCat_d_inv_eq_zero_iff
    (cyclicTotalDifferential R A M) (cyclicTotalComplex_d R A M)]

/-- The class of a total cocycle in the cohomology of the total complex. -/
def cyclicTotalHomologyMk (n : ℕ) :
    LinearMap.ker (cyclicTotalDifferential R A M n) →ₗ[R] (cyclicTotalComplex R A M).homology n :=
  (cyclicTotalComplex R A M).moduleCatCohomologyClassOfIso (fun n ↦ cyclicTotalCochains R A M n)
    (fun n ↦ LinearMap.ker (cyclicTotalDifferential R A M n)) (cyclicTotalComplexXIso R A M)
    (mem_ker_cyclicTotalDifferential_iff R A M) n

variable {R A M}

/-- The class of a total cocycle is the homology class of any cycle of the total complex whose
underlying total cochain is that cocycle. -/
theorem cyclicTotalHomologyMk_eq_homologyπ {n : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M n)) (z : (cyclicTotalComplex R A M).cycles n)
    (hz : (cyclicTotalComplexXIso R A M n).hom ((cyclicTotalComplex R A M).iCycles n z) = x.1) :
    cyclicTotalHomologyMk R A M n x = (cyclicTotalComplex R A M).homologyπ n z :=
  (cyclicTotalComplex R A M).moduleCatCohomologyClassOfIso_eq_homologyπ _ _ _
    (mem_ker_cyclicTotalDifferential_iff R A M) x z hz

/-- Every class in the cohomology of the total complex is the class of a total cocycle. -/
theorem cyclicTotalHomologyMk_surjective (n : ℕ) :
    Function.Surjective (cyclicTotalHomologyMk R A M n) :=
  (cyclicTotalComplex R A M).moduleCatCohomologyClassOfIso_surjective _ _ _
    (mem_ker_cyclicTotalDifferential_iff R A M) n

/-- A total cocycle of degree zero has zero class exactly when it vanishes. -/
@[simp]
theorem cyclicTotalHomologyMk_zero_eq_zero_iff
    (x : LinearMap.ker (cyclicTotalDifferential R A M 0)) :
    cyclicTotalHomologyMk R A M 0 x = 0 ↔ x = 0 := by
  rw [cyclicTotalHomologyMk,
    (cyclicTotalComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff_exists
      _ _ _ _ CochainComplex.prev_nat_zero, (cyclicTotalComplex R A M).shape 0 0 (by simp)]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  refine ⟨fun ⟨_, h⟩ ↦ Subtype.ext ?_, fun h ↦ ⟨0, by simp [h]⟩⟩
  exact ((cyclicTotalComplexXIso R A M 0).inv_hom_id_apply x.1).symm.trans
    (by rw [← h, map_zero])

/-- A total cocycle of degree `n + 1` has zero class exactly when it is a total coboundary. -/
@[simp]
theorem cyclicTotalHomologyMk_succ_eq_zero_iff {n : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M (n + 1))) :
    cyclicTotalHomologyMk R A M (n + 1) x = 0 ↔ ∃ w, cyclicTotalDifferential R A M n w = x.1 := by
  rw [cyclicTotalHomologyMk,
    (cyclicTotalComplex R A M).moduleCatCohomologyClassOfIso_eq_zero_iff_exists
      _ _ _ _ (CochainComplex.prev_nat_succ n)]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨(cyclicTotalComplexXIso R A M n).hom w, ?_⟩,
    fun ⟨w, hw⟩ ↦ ⟨(cyclicTotalComplexXIso R A M n).inv w, ?_⟩⟩
  · rw [← cyclicTotalComplex_d_apply, hw, Iso.inv_hom_id_apply]
  · apply (ModuleCat.mono_iff_injective (cyclicTotalComplexXIso R A M (n + 1)).hom).1
      inferInstance
    rw [cyclicTotalComplex_d_apply, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, hw]

/-- A cyclic cocycle, included into column zero, is a total cocycle. -/
theorem cyclicCochainsToTotal_mem_ker {m : ℕ} (φ : cyclicCocycles R A M m) :
    cyclicCochainsToTotal R A M m φ.1 ∈ LinearMap.ker (cyclicTotalDifferential R A M m) := by
  rw [LinearMap.mem_ker, cyclicTotalDifferential_cyclicCochainsToTotal]
  convert map_zero (cyclicCochainsToTotal R A M (m + 1))
  exact Subtype.ext (by
    rw [coe_cyclicHochschildCoboundary_apply]
    exact (mem_cyclicCocycles_iff R A M).1 φ.2)

end Classes

section CohomologyClasses

variable {R : Type*} {A : Type u} {M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

/-- The inclusion of cyclic cochains into column zero sends the class of a cyclic cocycle to the
class of the corresponding total cocycle. -/
@[simp]
theorem homologyMap_cyclicCochainComplexToTotal_mk {m : ℕ} (φ : cyclicCocycles R A M m) :
    HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) m
        (cyclicCohomology.mk R A M m φ) =
      cyclicTotalHomologyMk R A M m ⟨_, cyclicCochainsToTotal_mem_ker φ⟩ := by
  rw [cyclicCohomology.mk_eq_homologyπ R A M φ ((cyclicCochainComplex R A M).moduleCatCyclesMk
      ((cyclicCochainComplexXIso R A M m).inv φ.1) (m + 1) (CochainComplex.next ℕ m)
      ((mem_cyclicCocycles_iff_complex R A M m φ.1).1 φ.2)) (by simp),
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  exact (cyclicTotalHomologyMk_eq_homologyπ _ _
    (by simp [cyclicCochainComplexToTotal_f_apply])).symm

end CohomologyClasses

end TauCeti
