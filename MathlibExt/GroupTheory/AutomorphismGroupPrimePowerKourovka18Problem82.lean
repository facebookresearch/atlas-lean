/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Transfer
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Prime powers in the order of a finite group's automorphism group

Green's theorem gives a uniform exponent for Kourovka Notebook Problem 18.82.
We take `f(n) = n² + 3n`. If conjugation by a Sylow `p`-subgroup gives too few
automorphisms, transfer gives a large abelian quotient. Homomorphisms from this quotient
into a central subgroup supply the required automorphisms.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismGroupPrimePowerKourovka18Problem82Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.82 (R. M.
Patne). UnsolvedMath record UM-00701511 (`KOU-18.82`), dataset ulamai/UnsolvedMath v1.8.0.

`Aut G` is `MulAut G`; `f` does not depend on `p`.
-/

/-- **Patne's prime-power divisibility problem (Kourovka 18.82).** The statement that there is a
function $f : \mathbb{N} \to \mathbb{N}$ such that for every $n \in \mathbb{N}$, every prime $p$ and
every finite group $G$, if $p^{f(n)}$ divides $|G|$ then $p^n$ divides $|\mathrm{Aut}(G)|$, where
$\mathrm{Aut}(G)$ is the group of automorphisms of $G$. -/
def autOrderPrimePowerBound : Prop :=
  ∃ f : ℕ → ℕ, ∀ n p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G],
    p ^ f n ∣ Nat.card G → p ^ n ∣ Nat.card (MulAut G)

open Subgroup
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime]

private lemma card_restrict_le {G B : Type*} [Group G] [Group B] [Finite G]
    (f : G →* B) (H : Subgroup G) :
    Nat.card H ≤ Nat.card f.ker * Nat.card (H.map f) := by
  let g := f.comp H.subtype
  have hk : Nat.card g.ker ∣ Nat.card f.ker :=
    card_comap_dvd_of_injective f.ker H.subtype H.subtype_injective
  rw [← card_ker_mul_card_range g, MonoidHom.range_comp, range_subtype]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd Nat.card_pos hk)

-- In a p-group of central index p^a the derived group has order at most p^(a²).
private lemma derived_bound (a : ℕ) (G : Type*) [Group G] [Finite G] (hG : IsPGroup p G)
    (ha : (center G).index ≤ p ^ a) : Nat.card (commutator G) ≤ p ^ (a * a) := by
  induction a generalizing G with
  | zero =>
    have h : center G = ⊤ := index_eq_one.mp (le_antisymm (by simpa only [pow_zero] using ha)
      (center G).index_pos)
    simp [(commutator_eq_bot_iff_center_eq_top G).mpr h]
  | succ a ih =>
    by_cases hc : center G = ⊤
    · simp [(commutator_eq_bot_iff_center_eq_top G).mpr hc, Nat.one_le_pow _ _ hp.out.pos]
    let q := QuotientGroup.mk' (center G)
    have hQ := hG.to_quotient (center G)
    have : Nontrivial (G ⧸ center G) := Finite.one_lt_card_iff_nontrivial.mp
      ((center G).one_lt_index_of_ne_top hc)
    have := hQ.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : center (G ⧸ center G))
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center G) z.val
    have hxc (y : G) : ⁅x, y⁆ ∈ center G := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ⁅x, y⁆ = 1
      rw [map_commutatorElement, show q x = z.val from hx, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp z.property _).symm
    -- Killing the image of this homomorphism makes x central in the quotient.
    let d : G →* G :=
      { toFun := fun y => ⁅x, y⁆
        map_one' := commutatorElement_one_right _
        map_mul' := fun b c => by
          rw [commutatorElement_mul_right_eq_mul_conj,
            mul_assoc ⁅x, b⁆ b, mem_center_iff.mp (hxc c) b]
          group }
    have hd : d.range ≤ center G := by
      rintro _ ⟨y, rfl⟩
      exact hxc y
    have hker : center G ≤ d.ker := fun y hy =>
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hy x)
    have hcard : Nat.card d.range ≤ p ^ (a + 1) := by
      rw [← index_ker]
      exact (index_antitone hker).trans ha
    have := normal_of_le_center hd
    let π := QuotientGroup.mk' d.range
    have hl : center G < (center (G ⧸ d.range)).comap π := by
      refine lt_of_le_of_ne ?_ ?_
      · intro y hy
        apply mem_center_iff.mpr
        intro b
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective d.range b
        simpa only [map_mul] using congrArg π (mem_center_iff.mp hy g)
      · intro he
        have hmem : x ∈ (center (G ⧸ d.range)).comap π := by
          apply mem_center_iff.mpr
          intro b
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective d.range b
          apply Eq.symm
          apply commutatorElement_eq_one_iff_mul_comm.mp
          rw [← map_commutatorElement π]
          exact (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
        rw [← he] at hmem
        exact hz (Subtype.ext (hx ▸ (QuotientGroup.eq_one_iff _).mpr hmem))
    have hπ := hG.to_quotient d.range
    obtain ⟨k, hk⟩ := (hπ.to_quotient (center _)).exists_card_eq
    have hs := index_strictAnti hl
    rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at hs
    have hk' : (center (G ⧸ d.range)).index = p ^ k := hk
    have hka : k < a + 1 := (pow_lt_pow_iff_right₀ hp.out.one_lt).mp
      (hk' ▸ hs.trans_le ha)
    have hi := ih (G ⧸ d.range) hπ (hk' ▸ Nat.pow_le_pow_right hp.out.pos (by omega : k ≤ a))
    have hd' := card_restrict_le π (commutator G)
    rw [QuotientGroup.ker_mk',
      map_commutator_of_surjective (QuotientGroup.mk'_surjective _)] at hd'
    exact hd'.trans <| (Nat.mul_le_mul hcard hi).trans <| by
      rw [← pow_add]
      apply Nat.pow_le_pow_right hp.out.pos
      nlinarith

private lemma cyclic_hom_card (B D : Type*) [Group B] [IsCyclic B] [CommGroup D]
    [Finite B] [Finite D] (hB : IsPGroup p B) (hD : IsPGroup p D) :
    min (Nat.card B) (Nat.card D) ≤ Nat.card (B →* D) := by
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  obtain ⟨d, hd⟩ := hD.exists_card_eq
  have hm : p ^ min b d ≤ Nat.card D := hd ▸ Nat.pow_le_pow_right hp.out.pos (min_le_right ..)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp.out hD hm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := B)
  have horder (x : H) : orderOf (x : D) ∣ orderOf g := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hb]
    exact (orderOf_dvd_natCard x).trans (hH ▸ pow_dvd_pow p (min_le_left b d))
  have hinj : Function.Injective (fun x : H => monoidHomOfForallMemZpowers hg (horder x)) := by
    intro x y h
    exact Subtype.ext (by simpa using DFunLike.congr_fun h g)
  rw [hb, hd, ← (pow_right_mono₀ hp.out.one_le).map_min, ← hH]
  have : Finite (B →* D) := .of_injective _ DFunLike.coe_injective
  exact Nat.card_le_card_of_injective _ hinj

-- Decompose the domain into cyclic factors and count the choices of generator images.
private lemma hom_card (B D : Type*) [CommGroup B] [CommGroup D] [Finite B] [Finite D]
    (hB : IsPGroup p B) (hD : IsPGroup p D) :
    min (Nat.card B) (Nat.card D) ≤ Nat.card (B →* D) := by
  classical
  obtain ⟨ι, _, m, hm, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite B
  let M (i : ι) := Multiplicative (ZMod (m i))
  have (i : ι) : NeZero (m i) := ⟨(hm i).ne_zero⟩
  have (i : ι) : Finite (M i) := inferInstanceAs (Finite (Multiplicative (ZMod (m i))))
  have (i : ι) : Finite (M i →* D) := .of_injective _ DFunLike.coe_injective
  have h (i : ι) : min (Nat.card (M i)) (Nat.card D) ≤ Nat.card (M i →* D) :=
    cyclic_hom_card (M i) D ((hB.of_equiv e).of_surjective (Pi.evalMonoidHom M i)
      (Function.surjective_eval i)) hD
  have he := (e.monoidHomCongrLeft (N := D)).trans (Pi.monoidHomMulEquiv M D)
  rw [Nat.card_congr he.toEquiv, Nat.card_pi]
  by_cases hc : ∃ i, Nat.card D ≤ Nat.card (M i)
  · obtain ⟨i, hi⟩ := hc
    exact (min_le_right ..).trans <| (min_eq_right hi ▸ h i).trans
      (Finset.single_le_prod (f := fun j => Nat.card (M j →* D)) (fun j _ => Nat.card_pos)
        (Finset.mem_univ i))
  · push Not at hc
    refine (min_le_left ..).trans ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    exact Finset.prod_le_prod fun i _ => min_eq_left (hc i).le ▸ h i

-- Every homomorphism to a central subgroup killed by q gives a shear automorphism.
private lemma twist_dvd {G B D : Type*} [Group G] [Group B] [CommGroup D]
    (q : G →* B) (hq : Function.Surjective q) (j : D →* G) (hj : Function.Injective j)
    (hc : ∀ d, j d ∈ center G) (hk : ∀ d, q (j d) = 1) :
    Nat.card (B →* D) ∣ Nat.card (MulAut G) := by
  let t (f : B →* D) (x : G) := j (f (q x)) * x
  have ht (f g : B →* D) (x : G) : t f (t g x) = t (f * g) x := by
    simp [t, hk, mul_assoc]
  have ho (x : G) : t 1 x = x := by simp [t]
  let T : (B →* D) →* MulAut G :=
    { toFun f :=
        { toFun := t f
          invFun := t f⁻¹
          left_inv := fun x => by rw [ht, inv_mul_cancel, ho]
          right_inv := fun x => by rw [ht, mul_inv_cancel, ho]
          map_mul' := fun x y => by
            simp only [t, map_mul, mul_assoc]
            rw [← mul_assoc x, mem_center_iff.mp (hc _) x, mul_assoc] }
      map_one' := by ext x; exact ho x
      map_mul' := fun f g => by ext x; exact (ht f g x).symm }
  apply card_dvd_of_injective T
  intro f g h
  ext b
  obtain ⟨x, rfl⟩ := hq b
  exact hj (mul_right_cancel (show t f x = t g x from DFunLike.congr_fun h x))

-- Transfer on central elements of P is abelianization followed by the [G : P]-th power map.
private lemma central_transfer_bound {G : Type*} [Group G] [Finite G] (P : Sylow p G)
    (C : Subgroup P) (hc : ∀ x ∈ C, (x : G) ∈ center G) :
    Nat.card C ≤ Nat.card (commutator P) *
      Nat.card (MonoidHom.transfer (H := (P : Subgroup G)) Group.Abelianization.of).range := by
  let ab : P →* Group.Abelianization P := Group.Abelianization.of
  let t := MonoidHom.transfer (H := (P : Subgroup G)) ab
  have him : C.map ab ≤ t.range := by
    rintro _ ⟨x, hx, rfl⟩
    have hcop := hp.out.coprime_iff_not_dvd.mpr P.not_dvd_index
    obtain ⟨y, hy⟩ := ((P.isPGroup.to_subgroup C).powEquiv hcop).surjective ⟨x, hx⟩
    change y ^ (P : Subgroup G).index = _ at hy
    refine ⟨y.val.val, ?_⟩
    have hz := hc y y.property
    have key (k : ℕ) (g : G) (_ : g⁻¹ * (y.val.val ^ k) * g ∈ (P : Subgroup G)) :
        g⁻¹ * (y.val.val ^ k) * g = y.val.val ^ k := by
      rw [mem_center_iff.mp ((center G).pow_mem hz k) g⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    change MonoidHom.transfer ab _ = _
    rw [MonoidHom.transfer_eq_pow ab _ key]
    exact congrArg ab (congrArg Subtype.val hy)
  have h := card_restrict_le ab C
  rw [show ab.ker = commutator P from Group.Abelianization.ker_of P] at h
  exact h.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le him))

private lemma pow_dvd_of_le {B : Type*} [Group B] [Finite B] (hB : IsPGroup p B) {n : ℕ}
    (h : p ^ n ≤ Nat.card B) : p ^ n ∣ Nat.card B := by
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  rw [hb] at h ⊢
  exact pow_dvd_pow _ ((Nat.pow_le_pow_iff_right hp.out.one_lt).mp h)

private lemma central_twists {G A D : Type*} [Group G] [CommGroup A] [CommGroup D]
    [Finite A] [Finite D] (hA : IsPGroup p A) (hD : IsPGroup p D)
    (t : G →* A) (j : D →* G) (hj : Function.Injective j) (hc : ∀ d, j d ∈ center G)
    (n : ℕ) (hd : Nat.card D = p ^ n) (ht : p ^ n * p ^ n ≤ Nat.card t.range) :
    p ^ n ∣ Nat.card (MulAut G) := by
  -- Quotienting by t(D) makes the twists fix D pointwise.
  let u := t.rangeRestrict
  let K := (u.comp j).range
  let B := t.range ⧸ K
  let q := (QuotientGroup.mk' K).comp u
  have hK : Nat.card K ≤ p ^ n := hd ▸ Nat.le_of_dvd Nat.card_pos (card_range_dvd (u.comp j))
  have hB : p ^ n ≤ Nat.card B := by
    apply Nat.le_of_mul_le_mul_left (c := p ^ n)
    · exact ht.trans (K.card_mul_index ▸ Nat.mul_le_mul_right _ hK)
    · exact pow_pos hp.out.pos _
  have hPB := (hA.to_subgroup t.range).to_quotient K
  have : Finite (B →* D) := .of_injective _ DFunLike.coe_injective
  have hPD : IsPGroup p (B →* D) := by
    obtain ⟨d, he⟩ := hD.exists_card_eq
    intro f
    exact ⟨d, by ext x; simp [← he]⟩
  apply (pow_dvd_of_le hPD ((le_min hB hd.ge).trans (hom_card B D hPB hD))).trans
  apply twist_dvd q ((QuotientGroup.mk'_surjective K).comp t.rangeRestrict_surjective) j hj hc
  exact fun d => (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩

private lemma bound_for_group (n : ℕ) {G : Type*} [Group G] [Finite G]
    (h : p ^ (n * n + 3 * n) ∣ Nat.card G) : p ^ n ∣ Nat.card (MulAut G) := by
  let P : Sylow p G := default
  let c := MulAut.conj.comp (P : Subgroup G).subtype
  let C := c.ker
  have hP := P.isPGroup
  have hI := hP.of_surjective c.rangeRestrict c.rangeRestrict_surjective
  by_cases hi : p ^ n ≤ Nat.card c.range
  · exact (pow_dvd_of_le hI hi).trans c.range.card_subgroup_dvd_card
  have hc (x : P) (hx : x ∈ C) : (x : G) ∈ center G := by
    apply mem_center_iff.mpr
    intro y
    have he : MulAut.conj (x : G) = 1 := hx
    have := DFunLike.congr_fun he y
    change ↑x * y * (↑x)⁻¹ = y at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have hCP : C ≤ center P := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc x hx) y)
  have hi' : C.index ≤ p ^ n := (index_ker c).trans_le (le_of_not_ge hi)
  have hder := derived_bound n P hP ((index_antitone hCP).trans hi')
  let t := MonoidHom.transfer (H := (P : Subgroup G))
    (Group.Abelianization.of : P →* Group.Abelianization P)
  have hC : p ^ (n * n) * (p ^ n * p ^ n) ≤ Nat.card C := by
    apply Nat.le_of_mul_le_mul_right (c := p ^ n)
    · calc
        _ = p ^ (n * n + 3 * n) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
        _ ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos (P.pow_dvd_card_of_pow_dvd_card h)
        _ = Nat.card C * C.index := C.card_mul_index.symm
        _ ≤ _ := Nat.mul_le_mul_left _ hi'
    · exact pow_pos hp.out.pos _
  have ht : p ^ n * p ^ n ≤ Nat.card t.range := by
    apply Nat.le_of_mul_le_mul_left (c := p ^ (n * n))
    · exact hC.trans ((central_transfer_bound P C hc).trans (Nat.mul_le_mul_right _ hder))
    · exact pow_pos hp.out.pos _
  have hnC : p ^ n ≤ Nat.card C := by
    apply le_trans _ hC
    rw [← mul_assoc]
    exact Nat.le_mul_of_pos_left _ (mul_pos (pow_pos hp.out.pos _) (pow_pos hp.out.pos _))
  obtain ⟨D, hd⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp.out (hP.to_subgroup C) hnC
  let j := (P : Subgroup G).subtype.comp (C.subtype.comp D.subtype)
  have hj : Function.Injective j :=
    (P : Subgroup G).subtype_injective.comp (C.subtype_injective.comp D.subtype_injective)
  have hjc (d : D) : j d ∈ center G := hc d.val.val d.val.property
  let : CommGroup D := { (inferInstance : Group D) with
    mul_comm := fun x y => hj (by simpa using mem_center_iff.mp (hjc y) (j x)) }
  exact central_twists (hP.to_quotient (commutator P)) (IsPGroup.of_card hd) t j hj hjc n hd ht

/--
**Green's theorem on prime powers dividing the order of the automorphism group (Kourovka 18.82).**
There is a function $f : \mathbb{N} \to \mathbb{N}$, the same for all primes, such that for every
$n \in \mathbb{N}$, every prime $p$ and every finite group $G$, if $p^{f(n)}$ divides $|G|$ then
$p^n$ divides $|\mathrm{Aut}(G)|$, where $\mathrm{Aut}(G)$ is the group of automorphisms of $G$.

Ledermann and Neumann (1956) first proved this with a function depending on $p$; J. A. Green (1956)
obtained a function independent of $p$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.82 (R. M.
Patne); resolution: J. A. Green, Proc. Roy. Soc. London Ser. A 237 (1956), 574-581 (improving W.
Ledermann and B. H. Neumann, Proc. Roy. Soc. London Ser. A 235 (1956), 235-246), Kourovka Archive,
Problem 18.82: Yes, there is, https://arxiv.org/abs/1401.0300v49.
-/
public theorem autOrderPrimePowerBound_holds : autOrderPrimePowerBound := by
  refine ⟨fun n => n * n + 3 * n, ?_⟩
  intro n p hp G _ _ hG
  have : Fact p.Prime := ⟨hp⟩
  exact bound_for_group n hG

end MathlibExt.GroupTheory.AutomorphismGroupPrimePowerKourovka18Problem82Wanted
