/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.BurnsidePaqb.SolvableInduction
public import MathlibExt.GroupTheory.BurnsidePaqb.KillingLemma
public import MathlibExt.GroupTheory.BurnsidePaqb.ScalarCenter
public import MathlibExt.GroupTheory.BurnsidePaqb.CharacterOrthogonality

/-!
Simple-prime-power stage of the complete Burnside proof.

Authors: Muse Spark 1.3, @toskua, Avocado
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/SimplePrime.lean`.
-/

namespace BurnsidePaqb

@[expose] public section

variable {G : Type*} [Group G] [Fintype G]

/-- **An algebraic integer cannot solve $1 + p\beta = 0$ for a prime $p$.** Let $p$ be a prime
number. There is no algebraic integer $\beta \in \mathbb{C}$ with $1 + p\beta = 0$, since such a
$\beta$ would make $-1/p$ an algebraic integer. -/
theorem false_of_one_add_prime_mul_isIntegral {p : ℕ} (hp : p.Prime)
    {β : ℂ} (hβ : IsIntegral ℤ β) (h : 1 + (p : ℂ) * β = 0) : False := by
  have hβeq : β = -1 / (p : ℂ) := by
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h1 : (p : ℂ) * β = -1 := eq_neg_of_add_eq_zero_right h
    rw [eq_div_iff hp0, mul_comm]
    exact h1
  have hβq : IsIntegral ℤ (-1 / (p : ℚ)) := by
    haveI : IsScalarTower ℤ ℚ ℂ := IsScalarTower.of_algebraMap_eq fun x => by simp
    have hiff :=
      isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ) (x := -1 / (p : ℚ))
    apply hiff.mp
    have e : algebraMap ℚ ℂ (-1 / (p : ℚ)) = β := by
      rw [eq_ratCast, hβeq]
      push_cast
      ring
    rw [e]
    exact hβ
  have : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨n, hn⟩ := (isIntegrallyClosed_iff ℚ).mp inferInstance hβq
  have hcast : (n : ℚ) = -1 / (p : ℚ) := by simpa using hn
  have hpn : (p : ℚ) * n = -1 := by
    have hp0 : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [hcast]
    field_simp
  have hzz : (p : ℤ) * n = -1 := by exact_mod_cast hpn
  have hdvd : (p : ℤ) ∣ 1 := ⟨-n, by rw [mul_neg, hzz]; simp⟩
  have hdvdN : p ∣ 1 := by exact_mod_cast hdvd
  exact hp.not_dvd_one hdvdN

omit [Fintype G] in
/-- **One-dimensional representations act by their character.** Let $\rho$ be a representation
of a group $G$ on a complex vector space $V$ of dimension $1$, and let $\chi$ be the character of
$\rho$. Then for every $g \in G$ the operator $\rho(g)$ is multiplication by the scalar $\chi(g)$,
that is, $\rho(g) = \chi(g) \cdot \mathrm{id}_V$. -/
theorem eq_smul_one_of_finrank_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hd : Module.finrank ℂ V = 1) (g : G) :
    ρ g = ρ.character g • 1 := by
  have b := Module.finBasis ℂ V
  rw [hd] at b
  set d : ℂ := b.repr (ρ g (b 0)) 0 with hddef
  have hexpand : ∀ x : V, x = b.repr x 0 • b 0 := fun x => by
    have h := Module.Basis.sum_repr b x
    rw [Fin.sum_univ_one] at h
    exact h.symm
  have hfb0 : ρ g (b 0) = d • b 0 := hexpand _
  have hfg : ρ g = d • 1 := by
    apply Module.Basis.ext b
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [hfb0]
    simp
  have hχ : ρ.character g = d := by
    have htr : LinearMap.trace ℂ V (ρ g) = d := by
      rw [hfg, map_smul]
      simp [hd, smul_eq_mul]
    exact htr
  rw [hχ]
  exact hfg

open Classical in
/-- **A linear character as a homomorphism to $\mathbb{C}^\times$.** Let $G$ be a finite group and
let $\rho$ be a representation of $G$ on a complex vector space $V$ of dimension $1$, with
character $\chi$. This is the group homomorphism from $G$ to the multiplicative group
$\mathbb{C}^\times$ of nonzero complex numbers that sends $g$ to $\chi(g)$. -/
noncomputable def linearCharHom {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ G V)
    (hd : Module.finrank ℂ V = 1) : G →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ρ.character g
      map_one' := by rw [Representation.char_one, hd]; simp
      map_mul' := fun g h => by
        have h1 := eq_smul_one_of_finrank_one ρ hd g
        have h2 := eq_smul_one_of_finrank_one ρ hd h
        have h3 := eq_smul_one_of_finrank_one ρ hd (g * h)
        have hmul : ρ (g * h) = ρ g * ρ h := map_mul ρ g h
        have htr : ρ.character (g * h)
            = ρ.character g * ρ.character h := by
          have e : (ρ.character (g * h)) • (1 : Module.End ℂ V)
              = (ρ.character g * ρ.character h) • 1 := by
            rw [← h3, hmul, h1, h2, smul_mul_smul, one_mul]
          exact smul_left_injective ℂ (one_ne_zero : (1 : Module.End ℂ V) ≠ 0) e
        exact htr }

/-- **A simple group with a nontrivial linear character has prime order.** Let $G$ be a finite
simple group and let $\rho$ be a representation of $G$ on a complex vector space $V$ of
dimension $1$. If the character of $\rho$ is not the constant function $1$, then the order of
$G$ is a prime number. -/
theorem card_eq_prime_of_nontrivial_linear [IsSimpleGroup G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ G V)
    (hd : Module.finrank ℂ V = 1) (hne : ρ.character ≠ 1) :
    ∃ r : ℕ, r.Prime ∧ Fintype.card G = r := by
  set lam : G →* ℂˣ := linearCharHom ρ hd with hlamdef
  have hchar : ∀ g : G, ρ.character g = (lam g : ℂ) := fun g => rfl
  have hker_ne_top : lam.ker ≠ ⊤ := by
    intro hcon
    apply hne
    funext g
    have hg : g ∈ lam.ker := hcon ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hg
    rw [hchar g]
    have h1 : ((1 : ℂˣ) : ℂ) = 1 := Units.val_one
    rw [hg]
    exact h1
  have hker_cases := IsSimpleGroup.eq_bot_or_eq_top_of_normal lam.ker
  rcases hker_cases with hbot | htop
  · have hinj : Function.Injective lam :=
      (MonoidHom.ker_eq_bot_iff lam).mp hbot
    have hcomm : ∀ x y : G, x * y = y * x := fun x y =>
      hinj (by simp [map_mul, mul_comm])
    let : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    refine ⟨Fintype.card G, ?_, rfl⟩
    simpa only [Nat.card_eq_fintype_card] using
      (IsSimpleGroup.prime_card (α := G))
  · exact absurd htop hker_ne_top

/-- **Nonlinear irreducible characters of a simple group vanish on nonidentity classes of
coprime size.** Let $G$ be a finite simple group, let $\rho$ be an irreducible representation of
$G$ on a finite-dimensional complex vector space $V$ of dimension $d > 1$, and let $\chi$ be the
character of $\rho$. If $g \ne 1$ is an element of $G$ whose conjugacy class has size coprime to
$d$, then $\chi(g) = 0$. -/
theorem char_zero_of_nonlinear_of_coprime [IsSimpleGroup G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (g : G) (hne1 : g ≠ 1)
    (hd : 1 < Module.finrank ℂ V)
    (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V)) :
    ρ.character g = 0 := by
  rcases burnside_coprime_vanish ρ g hcop with hZ | h0
  · exfalso
    have hall := all_roots_eq_of_norm_eq ρ g hZ
    have hcard := charpoly_roots_card ρ g
    have hne0 : (ρ g).charpoly.roots ≠ 0 := by
      intro hz
      rw [hz, Multiset.card_zero] at hcard
      omega
    obtain ⟨μ₀, hμ₀⟩ := Multiset.exists_mem_of_ne_zero hne0
    have hμ : ∀ μ ∈ (ρ g).charpoly.roots, μ = μ₀ :=
      fun μ hμ => hall μ hμ μ₀ hμ₀
    have hsm := eq_smul_one_of_all_roots_eq ρ g μ₀ hμ
    have hgmem : g ∈ charCenter ρ := mem_charCenter_of_eq_smul ρ g μ₀ hsm
    have hproper : charCenter ρ ≠ ⊤ := charCenter_proper_of_nonlinear ρ hd
    have hbot : charCenter ρ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (charCenter ρ) with h | h
      · exact h
      · exact absurd h hproper
    have hmem : g ∈ (⊥ : Subgroup G) := hbot ▸ hgmem
    rw [Subgroup.mem_bot] at hmem
    exact hne1 hmem
  · exact h0

/-- **A simple group with a prime-power conjugacy class has prime order.** Let $G$ be a finite
simple group and let $g \ne 1$ be an element of $G$ whose conjugacy class has size $r^k$ for some
prime $r$ and some $k \ge 1$. Then the order of $G$ is a prime number.

Source: Bielefeld Corollary 6. -/
theorem cor6_of_prime_pow_class {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (g : G) (hg1 : g ≠ 1) (hpp : IsPrimePow (conjClass g).card) :
    ∃ r : ℕ, r.Prime ∧ Fintype.card G = r := by
  classical
  obtain ⟨rr, kk, hrrP, hk0, hclass⟩ := hpp
  have hrr : rr.Prime := Nat.prime_iff.mpr hrrP
  by_cases hab : ∀ x y : G, x * y = y * x
  · let : CommGroup G := { ‹Group G› with mul_comm := hab }
    refine ⟨Fintype.card G, ?_, rfl⟩
    simpa only [Nat.card_eq_fintype_card] using
      (IsSimpleGroup.prime_card (α := G))
  · by_cases hlin : ∃ c : Irr G, c ≠ Irr.triv G ∧
        Module.finrank ℂ ↥(Irr.repBundle G c).1 = 1 ∧
        Representation.character
          ((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1)
          ≠ 1
    · obtain ⟨c, hc, hd1, hne⟩ := hlin
      have := (Irr.repBundle G c).2
      have hirr := irreducible_of_simple_fdrep G (Irr.repBundle G c).1
      have := hirr
      have : Nontrivial ↥(Irr.repBundle G c).1 :=
        IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) (Representation.asModule
          (((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1)))
      exact card_eq_prime_of_nontrivial_linear _ hd1 hne
    · exfalso
      have hterm : ∀ c : Irr G, c ≠ Irr.triv G →
          ∃ β : ℂ, IsIntegral ℤ β ∧
            Irr.charFun G c 1 * Irr.charFun G c g = (rr : ℂ) * β := by
        intro c hc
        have := (Irr.repBundle G c).2
        have hirr : Representation.IsIrreducible
            ((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1) :=
          irreducible_of_simple_fdrep G (Irr.repBundle G c).1
        have := hirr
        set ρc : Representation ℂ G ↥(Irr.repBundle G c).1 :=
          ((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1)
          with hρc
        have : Nontrivial ↥(Irr.repBundle G c).1 :=
          IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρc.asModule
        have hchar : ∀ x, Irr.charFun G c x = ρc.character x :=
          fun x => Irr.charFun_eq_repBundle_char G c x
        have hdeg : Irr.charFun G c 1 =
            ((Module.finrank ℂ ↥(Irr.repBundle G c).1 : ℕ) : ℂ) :=
          Irr.charFun_one G c
        have hd : 1 ≤ Module.finrank ℂ ↥(Irr.repBundle G c).1 :=
          Module.finrank_pos
        by_cases hd1 : Module.finrank ℂ ↥(Irr.repBundle G c).1 = 1
        · have hch1 : ρc.character = 1 := by
            by_contra hne
            exact hlin ⟨c, hc, hd1, hne⟩
          exfalso
          apply hc
          have hfun : Irr.charFun G c = Irr.charFun G (Irr.triv G) := by
            funext x
            have e1 : Irr.charFun G c x = ρc.character x := hchar x
            have e2 : ρc.character x = 1 := by
              rw [hch1]
              exact Pi.one_apply x
            rw [e1, e2]
            exact (Irr.charFun_triv G x).symm
          exact Irr.charFun_inj G hfun
        · have hd2 : 1 < Module.finrank ℂ ↥(Irr.repBundle G c).1 := by omega
          by_cases hdiv : rr ∣ Module.finrank ℂ ↥(Irr.repBundle G c).1
          · refine ⟨((Module.finrank ℂ ↥(Irr.repBundle G c).1 / rr : ℕ) : ℂ) *
              Irr.charFun G c g, ?_, ?_⟩
            · rw [hchar g]
              exact (isIntegral_natCast _).mul (character_isIntegral _ _)
            · have hdm : rr * (Module.finrank ℂ ↥(Irr.repBundle G c).1 / rr)
                  = Module.finrank ℂ ↥(Irr.repBundle G c).1 :=
                Nat.mul_div_cancel' hdiv
              have e1 : Irr.charFun G c 1 = (rr : ℂ) *
                  ((Module.finrank ℂ ↥(Irr.repBundle G c).1 / rr : ℕ) : ℂ) := by
                rw [hdeg, ← Nat.cast_mul, hdm]
              rw [e1, hchar g]
              ring
          · have hcop : Nat.Coprime (conjClass g).card
                (Module.finrank ℂ ↥(Irr.repBundle G c).1) := by
              rw [← hclass]
              exact Nat.Coprime.pow_left kk ((hrr.coprime_iff_not_dvd).mpr hdiv)
            have hzero := char_zero_of_nonlinear_of_coprime ρc g hg1 hd2 hcop
            refine ⟨0, isIntegral_zero, ?_⟩
            rw [hchar g, hzero]
            simp
      have hsum := regular_character_vanishes G g hg1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Irr.triv G))] at hsum
      have htriv1 : Irr.charFun G (Irr.triv G) 1 * Irr.charFun G (Irr.triv G) g
          = 1 := by
        simp [Irr.charFun_triv]
      rw [htriv1] at hsum
      have hB : ∃ B : ℂ, IsIntegral ℤ B ∧
          ∑ c ∈ Finset.univ.erase (Irr.triv G),
            Irr.charFun G c 1 * Irr.charFun G c g = (rr : ℂ) * B := by
        have hch : ∀ c : Irr G, ∃ β : ℂ, (c ≠ Irr.triv G → IsIntegral ℤ β) ∧
            (c ≠ Irr.triv G → Irr.charFun G c 1 * Irr.charFun G c g
              = (rr : ℂ) * β) := by
          intro c
          by_cases hc : c = Irr.triv G
          · exact ⟨0, fun h => absurd hc h, fun h => absurd hc h⟩
          · obtain ⟨β, hβint, hβeq⟩ := hterm c hc
            exact ⟨β, fun _ => hβint, fun _ => hβeq⟩
        choose βf hβfint hβfeq using hch
        refine ⟨∑ c ∈ Finset.univ.erase (Irr.triv G), βf c, ?_, ?_⟩
        · exact IsIntegral.sum _
            (fun c hc => hβfint c (Finset.ne_of_mem_erase hc))
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl
            (fun c hc => hβfeq c (Finset.ne_of_mem_erase hc))
      obtain ⟨B, hBint, hBeq⟩ := hB
      rw [hBeq] at hsum
      exact false_of_one_add_prime_mul_isIntegral hrr hBint hsum

end

end BurnsidePaqb
