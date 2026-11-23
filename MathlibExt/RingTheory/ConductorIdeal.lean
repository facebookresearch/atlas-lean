/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

/-!
# Conductor ideal of a subalgebra

For a subalgebra `A` of a commutative `R`-algebra `S`, the conductor ideal of `A`
is the largest ideal of `S` contained in `A`: it consists of those `s : S` with
`s * t ∈ A` for every `t : S`. For `A = Algebra.adjoin R {x}` this recovers
Mathlib's element-generated conductor `conductor R x`.
-/

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Subalgebra

/-- **Conductor ideal of a subalgebra.** Let $R$ be a commutative semiring, $S$ a commutative
$R$-algebra and $A$ an $R$-subalgebra of $S$. The conductor ideal of $A$ is the ideal of $S$
consisting of all $s \in S$ such that $st \in A$ for every $t \in S$; it is the largest ideal of
$S$ contained in $A$. -/
def conductorIdeal (A : Subalgebra R S) : Ideal S where
  carrier := {s : S | ∀ t : S, s * t ∈ A}
  zero_mem' t := by simp
  add_mem' ha hb t := by simpa only [add_mul] using A.add_mem (ha t) (hb t)
  smul_mem' c a ha t := by
    simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * t)

/-- **Membership in the conductor ideal.** Let $R$ and $S$ be commutative semirings with $S$ an
$R$-algebra, and let $A$ be an $R$-subalgebra of $S$. An element $s \in S$ lies in the conductor
ideal of $A$ if and only if $st \in A$ for every $t \in S$. -/
theorem mem_conductorIdeal {A : Subalgebra R S} {s : S} :
    s ∈ A.conductorIdeal ↔ ∀ t : S, s * t ∈ A :=
  Iff.rfl

/-- **Universal property of the conductor ideal.** Let $R$ and $S$ be commutative semirings with
$S$ an $R$-algebra, let $A$ be an $R$-subalgebra of $S$, and let $I$ be an ideal of $S$. Then $I$
is contained in the conductor ideal of $A$ if and only if $I$ is contained in $A$. -/
theorem le_conductorIdeal_iff {A : Subalgebra R S} {I : Ideal S} :
    I ≤ A.conductorIdeal ↔ (I : Set S) ⊆ (A : Set S) := by
  constructor
  · intro h s hs
    have hmem := mem_conductorIdeal.mp (h hs)
    simpa using hmem 1
  · intro h s hs t
    exact h (I.mul_mem_right t hs)

/-- **The conductor ideal lies in the subalgebra.** Let $R$ be a commutative semiring, $S$ a
commutative $R$-algebra and $A$ an $R$-subalgebra of $S$. Then the conductor ideal of $A$ is
contained in $A$. -/
theorem conductorIdeal_subset (A : Subalgebra R S) :
    (A.conductorIdeal : Set S) ⊆ (A : Set S) :=
  le_conductorIdeal_iff.mp le_rfl

/-- **Monotonicity of the conductor ideal.** Let $R$ be a commutative semiring, $S$ a commutative
$R$-algebra and $A \subseteq B$ two $R$-subalgebras of $S$. Then the conductor ideal of $A$ is
contained in the conductor ideal of $B$. -/
theorem conductorIdeal_mono {A B : Subalgebra R S} (h : A ≤ B) :
    A.conductorIdeal ≤ B.conductorIdeal := by
  intro s hs
  rw [mem_conductorIdeal] at hs ⊢
  exact fun t => h (hs t)

/-- **Conductor ideal of the whole algebra.** Let $R$ be a commutative semiring and $S$ a
commutative $R$-algebra. The conductor ideal of $S$, viewed as an $R$-subalgebra of itself, is
the unit ideal $S$. -/
@[simp]
theorem conductorIdeal_top : (⊤ : Subalgebra R S).conductorIdeal = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_conductorIdeal]
  intro t
  exact Algebra.mem_top

/-- **The conductor ideal is the unit ideal only for the whole algebra.** Let $R$ be a
commutative semiring, $S$ a commutative $R$-algebra and $A$ an $R$-subalgebra of $S$. The
conductor ideal of $A$ is all of $S$ if and only if $A = S$. -/
theorem conductorIdeal_eq_top_iff {A : Subalgebra R S} :
    A.conductorIdeal = ⊤ ↔ A = ⊤ := by
  constructor
  · intro h
    rw [Algebra.eq_top_iff]
    intro x
    have hle : (⊤ : Ideal S) ≤ A.conductorIdeal := by rw [h]
    exact le_conductorIdeal_iff.mp hle trivial
  · rintro rfl
    exact conductorIdeal_top

variable {T : Type*} [CommSemiring T] [Algebra R T]

/-- **Preimage of a conductor ideal.** Let $R$ be a commutative semiring, $S$ and $T$ commutative
$R$-algebras, $f \colon S \to T$ a homomorphism of $R$-algebras and $B$ an $R$-subalgebra of
$T$. Then the preimage under $f$ of the conductor ideal of $B$ is contained in the conductor
ideal of the subalgebra $f^{-1}(B)$ of $S$. -/
theorem conductorIdeal_comap_le (f : S →ₐ[R] T) (B : Subalgebra R T) :
    (B.conductorIdeal).comap f.toRingHom ≤ (B.comap f).conductorIdeal := by
  intro x hx t
  rw [Subalgebra.mem_comap, map_mul]
  exact mem_conductorIdeal.mp (Ideal.mem_comap.mp hx) (f t)

/-- **Conductor of a monogenic subalgebra.** Let $R$ be a commutative ring, $S$ a commutative
$R$-algebra and $x \in S$. The conductor ideal of the subalgebra $R[x]$ of $S$ generated by $x$
equals the conductor of $x$, the ideal of all $a \in S$ such that $ab \in R[x]$ for every
$b \in S$. -/
theorem adjoin_conductorIdeal {R' S' : Type*} [CommRing R'] [CommRing S']
    [Algebra R' S'] (x : S') :
    (Algebra.adjoin R' ({x} : Set S')).conductorIdeal = conductor R' x :=
  Ideal.ext fun _ => Iff.rfl

end Subalgebra

namespace Subalgebra

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] (T : Subalgebra R K)

variable [IsFractionRing R K]

variable [IsDomain R]

/-- **A finite overring has nonzero conductor.** Let $R$ be an integral domain with fraction
field $K$, and let $T$ be an $R$-subalgebra of $K$ that is finitely generated as an $R$-module.
Then the conductor ideal of the image of $R$ in $T$ (the smallest $R$-subalgebra of $T$) is
nonzero. -/
theorem conductorIdeal_bot_ne_bot_of_finite [Module.Finite R ↥T] :
    (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := ↥T)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (s.map ⟨Subtype.val, Subtype.val_injective⟩)
  have hb0 : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hd0 : algebraMap R ↥T (b : R) ≠ 0 := by
    intro h
    apply hb0
    apply IsFractionRing.injective R K
    have hcongr : ((algebraMap R ↥T (b : R) : ↥T) : K) =
        ((algebraMap R ↥T (0 : R) : ↥T) : K) := by
      rw [h, map_zero]
    exact hcongr
  refine (Submodule.ne_bot_iff _).mpr ⟨algebraMap R ↥T (b : R), ?_, hd0⟩
  rw [Subalgebra.mem_conductorIdeal]
  intro t
  have ht : t ∈ Submodule.span R s := by rw [hs]; exact Submodule.mem_top
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp ht
  have key : ∀ x ∈ s, algebraMap R ↥T (b : R) * x ∈ (⊥ : Subalgebra R ↥T) := by
    intro x hx
    obtain ⟨r, hr⟩ :=
      RingHom.mem_rangeS.mp (hb (x : K) (Finset.mem_map.mpr ⟨x, hx, rfl⟩))
    have e1 : ((algebraMap R ↥T (b : R) * x : ↥T) : K)
        = algebraMap R K (b : R) * (x : K) := by simp
    have hval : ((algebraMap R ↥T (b : R) * x : ↥T) : K) = algebraMap R K r := by
      rw [e1, hr, Algebra.smul_def]
    have heq : algebraMap R ↥T (b : R) * x = algebraMap R ↥T r := Subtype.ext hval
    rw [heq]
    exact Algebra.mem_bot.mpr ⟨r, rfl⟩
  rw [← hf, Finset.mul_sum]
  exact sum_mem (fun x hx => by
    rw [Algebra.mul_smul_comm, Algebra.smul_def]
    exact (⊥ : Subalgebra R ↥T).mul_mem (Algebra.mem_bot.mpr ⟨_, rfl⟩) (key x hx))

variable [IsNoetherianRing R]

omit [IsFractionRing R K] [IsDomain R] in
/-- **A subalgebra of a field with nonzero conductor is finite.** Let $R$ be a Noetherian
commutative ring, $K$ a field that is an $R$-algebra, and $T$ an $R$-subalgebra of $K$. If the
conductor ideal of the image of $R$ in $T$ (the smallest $R$-subalgebra of $T$) is nonzero, then
$T$ is finitely generated as an $R$-module. -/
theorem finite_of_conductorIdeal_bot_ne_bot
    (h : (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥) : Module.Finite R ↥T := by
  obtain ⟨c, hc_mem, hc0⟩ := (Submodule.ne_bot_iff _).mp h
  have hcK : ((c : ↥T) : K) ≠ 0 := by
    rintro h0
    exact hc0 (Subtype.ext h0)
  have hmul_inj : Function.Injective (fun t : ↥T => c * t) := by
    intro a b hab
    have h2 : ((c * a : ↥T) : K) = ((c * b : ↥T) : K) := congrArg _ hab
    have hK : ((c : ↥T) : K) * (a : K) = ((c : ↥T) : K) * (b : K) := by
      simpa using h2
    have habK : (a : K) = (b : K) := mul_left_cancel₀ hcK hK
    exact Subtype.ext habK
  let g₀ : ↥T →ₗ[R] ↥T :=
    { toFun := fun t => c * t
      map_add' := fun a b => mul_add _ _ _
      map_smul' := fun r x => Algebra.mul_smul_comm _ _ _ }
  let g : ↥T →ₗ[R] ↥(⊥ : Subalgebra R ↥T) :=
    g₀.codRestrict (⊥ : Subalgebra R ↥T).toSubmodule
      (fun t => Subalgebra.mem_conductorIdeal.mp hc_mem t)
  have hg_inj : Function.Injective g :=
    fun a b hab => hmul_inj (congrArg Subtype.val hab)
  have hfin : Module.Finite R ↥(⊥ : Subalgebra R ↥T) := inferInstance
  have hFG : (Submodule.map g ⊤).FG := Submodule.FG.of_le hfin.fg_top le_top
  have hTop : (⊤ : Submodule R ↥T).FG :=
    Submodule.fg_of_fg_map_injective g hg_inj hFG
  exact Module.Finite.of_fg_top hTop

/-- **Finiteness of an overring via its conductor.** Let $R$ be a Noetherian integral domain with
fraction field $K$, and let $T$ be an $R$-subalgebra of $K$. Then the conductor ideal of the
image of $R$ in $T$ (the smallest $R$-subalgebra of $T$) is nonzero if and only if $T$ is
finitely generated as an $R$-module. -/
theorem bot_conductorIdeal_ne_bot_iff :
    (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥ ↔ Module.Finite R ↥T :=
  ⟨finite_of_conductorIdeal_bot_ne_bot T,
    fun h => @conductorIdeal_bot_ne_bot_of_finite _ _ _ _ _ T _ _ h⟩

/-- **Finiteness of the integral closure via the conductor.** Let $R$ be a Noetherian integral
domain with fraction field $K$, and let $\overline{R}$ be the integral closure of $R$ in $K$,
viewed as an $R$-algebra. The conductor ideal of the smallest $R$-subalgebra of $\overline{R}$
(the image of $R$) is a nonzero ideal of $\overline{R}$ if and only if $\overline{R}$ is finitely
generated as an $R$-module. -/
theorem integralClosure_bot_conductorIdeal_ne_bot_iff :
    (⊥ : Subalgebra R ↥(integralClosure R K)).conductorIdeal ≠ ⊥ ↔
      Module.Finite R ↥(integralClosure R K) :=
  bot_conductorIdeal_ne_bot_iff (integralClosure R K)

end Subalgebra
