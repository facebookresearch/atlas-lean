/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderIdeals
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

@[expose] public section

set_option autoImplicit false

/-!
# The order `ℤ + f𝒪_K`

Let `K` be a number field with ring of integers `𝒪_K = integralClosure ℤ K` and let `f` be a
positive integer. We define the subring `ℤ + f𝒪_K` of `K` (`NumberField.orderOfConductor`) and
prove:

* `NumberField.isOrder_orderOfConductor`: it is an order of `K`;
* `NumberField.orderOfConductor_one`: for `f = 1` it is `𝒪_K`;
* `NumberField.index_orderOfConductor`: for `K ≠ ℚ` of degree `n` it has index `f ^ (n - 1)`
  in `𝒪_K`;
* `NumberField.conductorIdeal_orderOfConductor`: for `K ≠ ℚ` its conductor is `f𝒪_K`;
* `NumberField.comap_algebraMap_span_natCast`: `f𝒪_K ∩ ℤ = fℤ`;
* `NumberField.ker_intCastRingHom_quotient_orderOfConductor` and
  `NumberField.quotientLift_intCastRingHom_bijective_orderOfConductor`: for `K ≠ ℚ`, the map
  `ℤ → ℤ + f𝒪_K` induces a ring isomorphism `ℤ/fℤ ≅ (ℤ + f𝒪_K)/f𝒪_K`;
* `NumberField.natCard_units_quotient_orderOfConductor`: so for `K ≠ ℚ` the unit group of the
  quotient of `ℤ + f𝒪_K` by its conductor has `φ(f)` elements.

Source: K. Conrad, *The conductor ideal of an order*, Example 2.2 (p. 2) and Remark 2.3 (p. 3).
-/

namespace NumberField

/-- **The order $\mathbb{Z} + f\mathcal{O}_K$.** Let $K$ be a number field with ring of integers
$\mathcal{O}_K$ (`integralClosure ℤ K`) and let $f$ be a natural number. This is the subring

$$\mathbb{Z} + f\mathcal{O}_K = \{m + fy : m \in \mathbb{Z},\ y \in \mathcal{O}_K\}$$

of $K$, as a $\mathbb{Z}$-subalgebra of $K$. For $f > 0$ it is an order of $K$
(`NumberField.isOrder_orderOfConductor`), and for $K \neq \mathbb{Q}$ its conductor is
$f\mathcal{O}_K$ (`NumberField.conductorIdeal_orderOfConductor`); for $f = 0$ it is $\mathbb{Z}$.

K. Conrad, *The conductor ideal of an order*, Example 2.2 (p. 2): "consider $a = c\mathcal{O}_K$
with $c \in \mathbb{Z}^+$ and take $K \neq \mathbb{Q}$ [...] We will show the order
$O = \mathbb{Z} + c\mathcal{O}_K$ has conductor $c\mathcal{O}_K$." -/
def orderOfConductor (K : Type*) [Field K] [NumberField K] (f : ℕ) : Subalgebra ℤ K where
  carrier := {x | ∃ (m : ℤ) (y : K), y ∈ integralClosure ℤ K ∧ x = m + f * y}
  mul_mem' := by
    rintro _ _ ⟨m, y, hy, rfl⟩ ⟨m', y', hy', rfl⟩
    refine ⟨m * m', m * y' + m' * y + f * y * y', ?_, by push_cast; ring⟩
    have hf : (f : K) ∈ integralClosure ℤ K := natCast_mem _ f
    have hm : (m : K) ∈ integralClosure ℤ K := intCast_mem _ m
    have hm' : (m' : K) ∈ integralClosure ℤ K := intCast_mem _ m'
    exact add_mem (add_mem (mul_mem hm hy') (mul_mem hm' hy)) (mul_mem (mul_mem hf hy) hy')
  add_mem' := by
    rintro _ _ ⟨m, y, hy, rfl⟩ ⟨m', y', hy', rfl⟩
    exact ⟨m + m', y + y', add_mem hy hy', by push_cast; ring⟩
  algebraMap_mem' r := ⟨r, 0, zero_mem _, by simp⟩

variable {K : Type*} [Field K] [NumberField K]

/-- **Membership in $\mathbb{Z} + f\mathcal{O}_K$.** Let $K$ be a number field and $f$ a natural
number. An element $x \in K$ lies in $\mathbb{Z} + f\mathcal{O}_K$ (`NumberField.orderOfConductor`)
if and only if $x = m + fy$ for some $m \in \mathbb{Z}$ and $y \in \mathcal{O}_K$. -/
theorem mem_orderOfConductor {f : ℕ} {x : K} :
    x ∈ orderOfConductor K f ↔
      ∃ (m : ℤ) (y : K), y ∈ integralClosure ℤ K ∧ x = m + f * y :=
  Iff.rfl

private theorem orderOfConductor_le (f : ℕ) : orderOfConductor K f ≤ integralClosure ℤ K := by
  rintro _ ⟨m, y, hy, rfl⟩
  exact add_mem (intCast_mem _ m) (mul_mem (natCast_mem _ f) hy)

/-- Every element of `K` has a nonzero integer multiple in `𝒪_K`. -/
private theorem exists_intCast_mul_mem (x : K) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : K) * x ∈ integralClosure ℤ K := by
  obtain ⟨n, hn, h⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset K)
  have hx : IsIntegral ℤ ((n : K) * x) := by
    simpa [zsmul_eq_mul] using h x (Finset.mem_singleton_self x)
  exact ⟨n, hn, hx⟩

/-- An algebraic integer of `K` whose product with a nonzero integer is an integer is itself an
integer (`ℤ` is integrally closed). -/
private theorem exists_intCast_eq_of_mul_eq {z : K} (hz : IsIntegral ℤ z) {n k : ℤ} (hn : n ≠ 0)
    (h : (n : K) * z = k) : ∃ y : ℤ, z = y := by
  have hn' : (n : K) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hzq : z = algebraMap ℚ K ((k : ℚ) / n) := by
    rw [map_div₀, map_intCast, map_intCast, ← h, mul_div_cancel_left₀ _ hn']
  rw [hzq] at hz
  have hq : IsIntegral ℤ ((k : ℚ) / n) :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ K).restrictScalars ℤ)
      (fun a b hab => (algebraMap ℚ K).injective hab)).mp hz
  obtain ⟨y, hy⟩ := hq.mem_range_ratCast_iff.mp ⟨(k : ℚ) / n, rfl⟩
  refine ⟨y, ?_⟩
  rw [hzq, ← hy, map_intCast]

/-- **$\mathbb{Z} + f\mathcal{O}_K$ is an order.** Let $K$ be a number field with ring of
integers $\mathcal{O}_K$ and let $f$ be a positive integer. Then $\mathbb{Z} + f\mathcal{O}_K$
(`NumberField.orderOfConductor`) is an order of $K$ (`NumberField.IsOrder`): it is contained in
$\mathcal{O}_K$ and its field of fractions is $K$.

K. Conrad, *The conductor ideal of an order*, Example 2.2 (p. 2): "the order
$O = \mathbb{Z} + c\mathcal{O}_K$" for $c \in \mathbb{Z}^+$. -/
theorem isOrder_orderOfConductor (f : ℕ) (hf : 0 < f) : IsOrder K (orderOfConductor K f) := by
  have hfK : (f : K) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  refine ⟨orderOfConductor_le f, ?_⟩
  exact
    { map_units := fun y => by
        rw [isUnit_iff_ne_zero]
        intro h
        exact nonZeroDivisors.ne_zero y.2 (Subtype.ext h)
      surj := fun z => by
        obtain ⟨n, hn, hnz⟩ := exists_intCast_mul_mem z
        have hn' : (n : K) ≠ 0 := Int.cast_ne_zero.mpr hn
        have hd : ((f * n : ℤ) : orderOfConductor K f) ≠ 0 := by
          intro h0
          have h1 := congrArg Subtype.val h0
          push_cast at h1
          exact mul_ne_zero hfK hn' h1
        refine ⟨⟨⟨(f : K) * (n * z), 0, (n : K) * z, hnz, by simp⟩,
          ⟨_, mem_nonZeroDivisors_of_ne_zero hd⟩⟩, ?_⟩
        change z * (((f * n : ℤ) : orderOfConductor K f) : K) = (f : K) * (n * z)
        push_cast
        ring
      exists_of_eq := fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩ }

/-- **$\mathbb{Z} + 1 \cdot \mathcal{O}_K = \mathcal{O}_K$.** For a number field $K$, the order
$\mathbb{Z} + f\mathcal{O}_K$ with $f = 1$ (`NumberField.orderOfConductor`) is the ring of
integers $\mathcal{O}_K$ (`integralClosure ℤ K`), as $\mathbb{Z}$-subalgebras of $K$. -/
theorem orderOfConductor_one : orderOfConductor K 1 = integralClosure ℤ K := by
  refine le_antisymm (orderOfConductor_le 1) fun x hx => ⟨0, x, hx, ?_⟩
  rw [Int.cast_zero, Nat.cast_one, one_mul, zero_add]

/-- If `m * t ∈ ℤ + f𝒪_K` for every `t ∈ 𝒪_K` and `[K : ℚ] ≥ 2`, then `f ∣ m`: the quotient
`𝒪_K / ℤ` is a nonzero free abelian group, and the coordinate of `m • e` along a basis vector `e`
of it is `m`. -/
private theorem natCast_dvd_of_forall_mul_mem (hK : 2 ≤ Module.finrank ℚ K) {f : ℕ} {m : ℤ}
    (h : ∀ t ∈ integralClosure ℤ K, ∃ (a : ℤ) (s : K), s ∈ integralClosure ℤ K ∧
      (m : K) * t = a + f * s) : (f : ℤ) ∣ m := by
  have : Module.Finite ℤ (integralClosure ℤ K) := (isOrder_integralClosure K).moduleFinite
  let N : Submodule ℤ (integralClosure ℤ K) := Submodule.span ℤ {1}
  have htf : Module.IsTorsionFree ℤ (integralClosure ℤ K ⧸ N) := by
    refine ⟨fun r hr u v huv => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective N u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N v
    change r • Submodule.Quotient.mk u = r • Submodule.Quotient.mk v at huv
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      at huv
    rw [Submodule.Quotient.eq]
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp huv
    have h1 : ((k • (1 : integralClosure ℤ K) : integralClosure ℤ K) : K) =
        ((r • u - r • v : integralClosure ℤ K) : K) := by rw [hk]
    simp only [zsmul_eq_mul] at h1
    push_cast at h1
    have h2 : (r : K) * ((u - v : integralClosure ℤ K) : K) = k := by
      push_cast
      linear_combination -h1
    obtain ⟨y, hy⟩ := exists_intCast_eq_of_mul_eq (u - v).2 hr0 h2
    refine Submodule.mem_span_singleton.mpr ⟨y, Subtype.ext ?_⟩
    rw [hy]
    simp
  have : Module.Free ℤ (integralClosure ℤ K ⧸ N) := Module.free_of_finite_type_torsion_free'
  have hnt : Nontrivial (integralClosure ℤ K ⧸ N) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply (show Module.finrank ℚ K ≠ 1 by omega)
    rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
    refine top_unique fun x _ => ?_
    obtain ⟨n, hn, hnx⟩ := exists_intCast_mul_mem x
    have h0 : Submodule.Quotient.mk (p := N) ⟨(n : K) * x, hnx⟩ = 0 := Subsingleton.elim _ _
    rw [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp h0
    have hk' : (k : K) = (n : K) * x := by
      have := congrArg Subtype.val hk
      simpa [zsmul_eq_mul] using this
    rw [Algebra.mem_bot]
    refine ⟨(k : ℚ) / n, ?_⟩
    rw [map_div₀, map_intCast, map_intCast, div_eq_iff (Int.cast_ne_zero.mpr hn), hk', mul_comm]
  let b := Module.Free.chooseBasis ℤ (integralClosure ℤ K ⧸ N)
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective N (b i)
  obtain ⟨a, s, hs, hmt⟩ := h t t.2
  have hR : (m • t : integralClosure ℤ K) =
      a • (1 : integralClosure ℤ K) + (f : ℤ) • (⟨s, hs⟩ : integralClosure ℤ K) := by
    apply Subtype.ext
    simp only [zsmul_eq_mul]
    push_cast
    rw [mul_one]
    exact hmt
  have hM : m • b i = (f : ℤ) • Submodule.Quotient.mk (p := N) ⟨s, hs⟩ := by
    have h1 : Submodule.Quotient.mk (p := N) (1 : integralClosure ℤ K) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.mem_span_singleton_self 1)
    have h2 := congrArg (Submodule.Quotient.mk (p := N)) hR
    simp only [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_add, h1, smul_zero,
      zero_add] at h2
    rw [← ht]
    exact h2
  have h3 := congrArg (fun w => b.repr w i) hM
  simp only [map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] at h3
  exact ⟨_, h3⟩

/-- **$f\mathcal{O}_K \cap \mathbb{Z} = f\mathbb{Z}$.** Let $K$ be a number field with ring of
integers $\mathcal{O}_K$ (`integralClosure ℤ K`) and let $f$ be a natural number. Then the
preimage of the principal ideal $f\mathcal{O}_K$ under $\mathbb{Z} \to \mathcal{O}_K$ is
$f\mathbb{Z}$: an integer $k$ lies in $f\mathcal{O}_K$ if and only if $f \mid k$.

K. Conrad, *The conductor ideal of an order*, Remark 2.3 (p. 3): "$a \cap \mathbb{Z} =
c\mathcal{O}_K \cap \mathbb{Z} = c\mathbb{Z}$" for $a = c\mathcal{O}_K$, $c \geq 2$; here any
$f \geq 0$ is allowed. -/
theorem comap_algebraMap_span_natCast (f : ℕ) :
    (Ideal.span {(f : integralClosure ℤ K)}).comap (algebraMap ℤ (integralClosure ℤ K)) =
      Ideal.span {(f : ℤ)} := by
  have : Module.FaithfullyFlat ℤ (integralClosure ℤ K) :=
    inferInstanceAs (Module.FaithfullyFlat ℤ (NumberField.RingOfIntegers K))
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := integralClosure ℤ K)
    (Ideal.span {(f : ℤ)})
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

/-- **The conductor of $\mathbb{Z} + f\mathcal{O}_K$.** Let $K \neq \mathbb{Q}$ be a number field
($[K : \mathbb{Q}] \geq 2$) with ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`), and let
$f$ be a natural number. Then the conductor
$\{x \in \mathcal{O}_K : x\mathcal{O}_K \subseteq \mathbb{Z} + f\mathcal{O}_K\}$ of
$\mathbb{Z} + f\mathcal{O}_K$ (`NumberField.orderOfConductor`; the conductor is
`Subalgebra.conductorIdeal` of $\mathbb{Z} + f\mathcal{O}_K$ viewed as a subring of
$\mathcal{O}_K$) is the principal ideal $f\mathcal{O}_K$.

K. Conrad, *The conductor ideal of an order*, Example 2.2 (p. 2): "consider $a = c\mathcal{O}_K$
with $c \in \mathbb{Z}^+$ and take $K \neq \mathbb{Q}$, so $n = [K : \mathbb{Q}] \geq 2$. We will
show the order $O = \mathbb{Z} + c\mathcal{O}_K$ has conductor $c\mathcal{O}_K$", concluding
"$O = \mathbb{Z} + c\mathcal{O}_K \implies \mathfrak{c}_O = c\mathbb{Z} + c\mathcal{O}_K =
c\mathcal{O}_K$" (with the conductor of Definition 1.1, p. 1). Conrad uses a $\mathbb{Z}$-basis
of $\mathcal{O}_K$ containing $1$; here we use that $\mathcal{O}_K/\mathbb{Z}$ is a nonzero free
abelian group. No positivity hypothesis on $f$ is needed: for $f = 0$ both sides are $0$. -/
theorem conductorIdeal_orderOfConductor (f : ℕ) (hK : 2 ≤ Module.finrank ℚ K) :
    ((orderOfConductor K f).comap (integralClosure ℤ K).val).conductorIdeal =
      Ideal.span {(f : integralClosure ℤ K)} := by
  refine le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr fun t => ?_)
  · obtain ⟨m, y, hy, hxy⟩ := Subalgebra.mem_conductorIdeal.mp hx 1
    have hxK : (x : K) = m + f * y := by simpa using hxy
    have hdvd : (f : ℤ) ∣ m := by
      refine natCast_dvd_of_forall_mul_mem hK fun t ht => ?_
      obtain ⟨a, s, hs, hts⟩ := Subalgebra.mem_conductorIdeal.mp hx ⟨t, ht⟩
      have hts' : (x : K) * t = a + f * s := by simpa using hts
      exact ⟨a, s - y * t, sub_mem hs (mul_mem hy ht), by linear_combination hts' - t * hxK⟩
    obtain ⟨c, hc⟩ := hdvd
    refine Ideal.mem_span_singleton'.mpr
      ⟨⟨(c : K) + y, add_mem (intCast_mem _ c) hy⟩, Subtype.ext ?_⟩
    push_cast
    rw [hxK, hc]
    push_cast
    ring
  · exact ⟨0, t, t.2, by simp⟩

/-- **$\mathbb{Z} \to (\mathbb{Z} + f\mathcal{O}_K)/\mathfrak{c}$ has kernel $f\mathbb{Z}$.** Let
$K \neq \mathbb{Q}$ be a number field ($[K : \mathbb{Q}] \geq 2$), let $f$ be a positive integer,
let $O = \mathbb{Z} + f\mathcal{O}_K$ (`NumberField.orderOfConductor`) and let $\mathfrak{c}$ be
its conductor, viewed as an ideal of $O$ (its preimage under $O \hookrightarrow \mathcal{O}_K$).
Then the kernel of the ring homomorphism $\mathbb{Z} \to O/\mathfrak{c}$ is $f\mathbb{Z}$.

K. Conrad, *The conductor ideal of an order*, Remark 2.3 (p. 3), for $a = c\mathcal{O}_K$:
"$a \cap \mathbb{Z} = c\mathcal{O}_K \cap \mathbb{Z} = c\mathbb{Z}$", with $\mathfrak{c} = a$ by
Example 2.2 (p. 2). -/
theorem ker_intCastRingHom_quotient_orderOfConductor (f : ℕ) (hf : 0 < f)
    (hK : 2 ≤ Module.finrank ℚ K) :
    RingHom.ker (Int.castRingHom ((orderOfConductor K f) ⧸ (((orderOfConductor K f).comap
      (integralClosure ℤ K).val).conductorIdeal.comap
        (Subalgebra.inclusion (isOrder_orderOfConductor f hf).le_integralClosure)))) =
      Ideal.span {(f : ℤ)} := by
  set I : Ideal (orderOfConductor K f) := ((orderOfConductor K f).comap
    (integralClosure ℤ K).val).conductorIdeal.comap
      (Subalgebra.inclusion (isOrder_orderOfConductor (K := K) f hf).le_integralClosure)
  ext k
  rw [RingHom.mem_ker, eq_intCast, ← map_intCast (Ideal.Quotient.mk I),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap, conductorIdeal_orderOfConductor f hK,
    map_intCast, ← comap_algebraMap_span_natCast (K := K) f, Ideal.mem_comap, eq_intCast]

/-- `ℤ → (ℤ + f𝒪_K)/𝔠` is surjective. -/
private theorem intCastRingHom_quotient_surjective (f : ℕ) (hf : 0 < f)
    (hK : 2 ≤ Module.finrank ℚ K) :
    Function.Surjective (Int.castRingHom ((orderOfConductor K f) ⧸ (((orderOfConductor K f).comap
      (integralClosure ℤ K).val).conductorIdeal.comap
        (Subalgebra.inclusion (isOrder_orderOfConductor f hf).le_integralClosure)))) := by
  set I : Ideal (orderOfConductor K f) := ((orderOfConductor K f).comap
    (integralClosure ℤ K).val).conductorIdeal.comap
      (Subalgebra.inclusion (isOrder_orderOfConductor (K := K) f hf).le_integralClosure)
  intro q
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨m, y, hy, hoy⟩ := o.2
  refine ⟨m, ?_⟩
  rw [eq_intCast, ← map_intCast (Ideal.Quotient.mk I), Ideal.Quotient.eq, Ideal.mem_comap,
    conductorIdeal_orderOfConductor f hK, Ideal.mem_span_singleton']
  refine ⟨⟨-y, neg_mem hy⟩, Subtype.ext ?_⟩
  change (-y) * f = (m : K) - (o : K)
  rw [hoy]
  ring

/-- **$\mathbb{Z}/f\mathbb{Z} \cong (\mathbb{Z} + f\mathcal{O}_K)/\mathfrak{c}$.** Let
$K \neq \mathbb{Q}$ be a number field ($[K : \mathbb{Q}] \geq 2$) with ring of integers
$\mathcal{O}_K$, let $f$ be a positive integer, let $O = \mathbb{Z} + f\mathcal{O}_K$
(`NumberField.orderOfConductor`) and let $\mathfrak{c} = f\mathcal{O}_K$ be its conductor
(`NumberField.conductorIdeal_orderOfConductor`), viewed as an ideal of $O$ (its preimage under
$O \hookrightarrow \mathcal{O}_K$). Then the ring homomorphism
$\mathbb{Z}/f\mathbb{Z} \to O/\mathfrak{c}$ induced by $\mathbb{Z} \to O$ is bijective, that is,
a ring isomorphism.

K. Conrad, *The conductor ideal of an order*, Remark 2.3 (p. 3), for $a = c\mathcal{O}_K$ with
$c \geq 2$: "Since $a \cap \mathbb{Z} = c\mathcal{O}_K \cap \mathbb{Z} = c\mathbb{Z}$,
$O/a = (\mathbb{Z} + a)/a \cong \mathbb{Z}/c\mathbb{Z}$ as rings"; here also $f = 1$ is allowed
(both rings are then zero). -/
theorem quotientLift_intCastRingHom_bijective_orderOfConductor (f : ℕ) (hf : 0 < f)
    (hK : 2 ≤ Module.finrank ℚ K) :
    Function.Bijective (Ideal.Quotient.lift (Ideal.span {(f : ℤ)})
      (Int.castRingHom ((orderOfConductor K f) ⧸ (((orderOfConductor K f).comap
        (integralClosure ℤ K).val).conductorIdeal.comap
          (Subalgebra.inclusion (isOrder_orderOfConductor f hf).le_integralClosure))))
      fun _ ha => RingHom.mem_ker.mp
        ((ker_intCastRingHom_quotient_orderOfConductor f hf hK).ge ha)) := by
  exact ⟨RingHom.lift_injective_of_ker_le_ideal _ _
      (ker_intCastRingHom_quotient_orderOfConductor f hf hK).le,
    Ideal.Quotient.lift_surjective_of_surjective _ _
      (intCastRingHom_quotient_surjective f hf hK)⟩

/-- **The units of $(\mathbb{Z} + f\mathcal{O}_K)/\mathfrak{c}$.** Let $K \neq \mathbb{Q}$ be a
number field ($[K : \mathbb{Q}] \geq 2$) with ring of integers $\mathcal{O}_K$, let $f$ be a
positive integer, let $O = \mathbb{Z} + f\mathcal{O}_K$ (`NumberField.orderOfConductor`) and let
$\mathfrak{c} = f\mathcal{O}_K$ be its conductor (`NumberField.conductorIdeal_orderOfConductor`),
viewed as an ideal of $O$. Then the unit group of $O/\mathfrak{c}$ has $\varphi(f)$ elements,
$\varphi$ being Euler's totient function, as
$O/\mathfrak{c} \cong \mathbb{Z}/f\mathbb{Z}$
(`NumberField.quotientLift_intCastRingHom_bijective_orderOfConductor`).

K. Conrad, *The conductor ideal of an order*, Remark 2.3 (p. 3): "$O/a = (\mathbb{Z} + a)/a
\cong \mathbb{Z}/c\mathbb{Z}$ as rings" for $a = c\mathcal{O}_K$. -/
theorem natCard_units_quotient_orderOfConductor (f : ℕ) (hf : 0 < f)
    (hK : 2 ≤ Module.finrank ℚ K) :
    Nat.card ((orderOfConductor K f) ⧸ (((orderOfConductor K f).comap
      (integralClosure ℤ K).val).conductorIdeal.comap
        (Subalgebra.inclusion (isOrder_orderOfConductor f hf).le_integralClosure)))ˣ =
      f.totient := by
  let e := RingEquiv.ofBijective _
    (quotientLift_intCastRingHom_bijective_orderOfConductor (K := K) f hf hK)
  have : NeZero f := ⟨hf.ne'⟩
  rw [← Nat.card_congr (Units.mapEquiv ((Int.quotientSpanNatEquivZMod f).symm.trans
    e).toMulEquiv).toEquiv, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- **The index of $\mathbb{Z} + f\mathcal{O}_K$ in $\mathcal{O}_K$.** Let $K \neq \mathbb{Q}$ be a
number field of degree $n = [K : \mathbb{Q}] \geq 2$ with ring of integers $\mathcal{O}_K$
(`integralClosure ℤ K`) and let $f$ be a positive integer. Then the additive subgroup
$\mathbb{Z} + f\mathcal{O}_K$ (`NumberField.orderOfConductor`, viewed inside $\mathcal{O}_K$) has
index $f^{n-1}$ in $\mathcal{O}_K$.

K. Conrad, *The conductor ideal of an order*, Example 2.2 (p. 2): "$\mathcal{O}_K/O \cong
\bigoplus_{i=2}^n \mathbb{Z}/c\mathbb{Z} \cong (\mathbb{Z}/c\mathbb{Z})^{n-1}$" for
$O = \mathbb{Z} + c\mathcal{O}_K$. Here we prove only the index, from the tower
$f\mathcal{O}_K \subseteq O \subseteq \mathcal{O}_K$ with $[\mathcal{O}_K : f\mathcal{O}_K] = f^n$
and $[O : f\mathcal{O}_K] = f$. -/
theorem index_orderOfConductor (f : ℕ) (hf : 0 < f) (hK : 2 ≤ Module.finrank ℚ K) :
    ((orderOfConductor K f).comap (integralClosure ℤ K).val).toSubmodule.toAddSubgroup.index =
      f ^ (Module.finrank ℚ K - 1) := by
  set ι := Subalgebra.inclusion (isOrder_orderOfConductor (K := K) f hf).le_integralClosure
  set O' := ((orderOfConductor K f).comap (integralClosure ℤ K).val).toSubmodule.toAddSubgroup
  set H := (Ideal.span {(f : integralClosure ℤ K)}).toAddSubgroup
  have hHO : H ≤ O' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨0, a, a.2, by simp [mul_comm]⟩
  have hrange : (ι : orderOfConductor K f →+ integralClosure ℤ K).range = O' := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      exact o.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcomap : H.comap (ι : orderOfConductor K f →+ integralClosure ℤ K) =
      (((orderOfConductor K f).comap (integralClosure ℤ K).val).conductorIdeal.comap
        ι).toAddSubgroup := by
    ext o
    rw [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Ideal.mem_comap, conductorIdeal_orderOfConductor f hK]
    rfl
  have hrel : H.relIndex O' = f := by
    rw [← hrange, ← AddSubgroup.index_comap, hcomap]
    change Submodule.cardQuot _ = f
    rw [Submodule.cardQuot_apply, ← Nat.card_congr (RingEquiv.ofBijective _
      (quotientLift_intCastRingHom_bijective_orderOfConductor (K := K) f hf hK)).toEquiv,
      Nat.card_congr (Int.quotientSpanNatEquivZMod f).toEquiv, Nat.card_zmod]
  have hH : H.index = f ^ Module.finrank ℚ K := by
    change Submodule.cardQuot _ = _
    rw [Submodule.cardQuot_apply]
    exact (isOrder_integralClosure K).natCard_quotient_natCast hf
  have h := AddSubgroup.relIndex_mul_index hHO
  rw [hrel, hH] at h
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℚ K = n + 1 :=
    ⟨_, (Nat.sub_add_cancel (by omega : 1 ≤ Module.finrank ℚ K)).symm⟩
  rw [hn, pow_succ'] at h
  rw [hn, Nat.add_sub_cancel]
  exact Nat.eq_of_mul_eq_mul_left hf h

end NumberField

end
