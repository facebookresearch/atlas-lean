/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamTightRootCutHallEquivalence












open Finset
open scoped symmDiff

namespace StatMech.FrontierA

variable {A B : Type*} [Fintype A] [Fintype B]



theorem card_le_bipartiteNeighbors_of_edgeDegree
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (hne : ∀ a ∈ S, (Finset.univ.filter (r a)).Nonempty)
    (hdeg : ∀ a ∈ S, ∀ b, r a b ->
      (Finset.univ.filter fun x => r x b).card <=
        (Finset.univ.filter (r a)).card) :
    S.card <= (Finset.univ.filter fun b => ∃ a ∈ S, r a b).card := by
  let LA : A -> Finset B := fun a => Finset.univ.filter (r a)
  let RB : B -> Finset A := fun b => Finset.univ.filter fun a => r a b
  let N : Finset B := Finset.univ.filter fun b => ∃ a ∈ S, r a b
  have hLApos : ∀ a ∈ S, 0 < (LA a).card := by
    intro a ha
    exact Finset.card_pos.mpr (hne a ha)
  have hRBpos : ∀ a ∈ S, ∀ b ∈ LA a, 0 < (RB b).card := by
    intro a ha b hb
    rw [Finset.card_pos]
    refine ⟨a, ?_⟩
    simpa [LA, RB] using hb
  have hLAN : ∀ a ∈ S, LA a ⊆ N := by
    intro a ha b hb
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, ha, by simpa [LA] using hb⟩
  have hleft : (S.card : ℚ) =
      ∑ a ∈ S, ∑ b ∈ LA a, (1 : ℚ) / (LA a).card := by
    calc
      (S.card : ℚ) = ∑ a ∈ S, (1 : ℚ) := by simp
      _ = ∑ a ∈ S, ∑ b ∈ LA a, (1 : ℚ) / (LA a).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_num [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hLApos a ha))]
  have hstep : (∑ a ∈ S, ∑ b ∈ LA a,
        (1 : ℚ) / (LA a).card) <=
      ∑ a ∈ S, ∑ b ∈ LA a, (1 : ℚ) / (RB b).card := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    apply one_div_le_one_div_of_le
    · exact_mod_cast hRBpos a ha b hb
    · exact_mod_cast hdeg a ha b (by simpa [LA] using hb)
  have hreindex : (∑ a ∈ S, ∑ b ∈ LA a,
        (1 : ℚ) / (RB b).card) =
      ∑ b ∈ N, ∑ a ∈ S,
        if r a b then (1 : ℚ) / (RB b).card else 0 := by
    calc
      _ = ∑ a ∈ S, ∑ b ∈ N,
          if r a b then (1 : ℚ) / (RB b).card else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.sum_filter]
        have hfilter : N.filter (r a) = LA a := by
          ext b
          simp only [N, LA, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · exact fun h => h.2
          · exact fun hab => ⟨⟨a, ha, hab⟩, hab⟩
        rw [hfilter]
      _ = _ := by rw [Finset.sum_comm]
  have hright : (∑ b ∈ N, ∑ a ∈ S,
        if r a b then (1 : ℚ) / (RB b).card else 0) <=
      (N.card : ℚ) := by
    calc
      _ <= ∑ b ∈ N, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro b hb
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hsub : (S.filter fun a => r a b).card <= (RB b).card := by
          apply Finset.card_le_card
          intro a ha
          simp only [Finset.mem_filter] at ha
          simp [RB, ha.2]
        have hpos : 0 < (RB b).card := by
          simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hb
          obtain ⟨a, haS, hab⟩ := hb
          exact hRBpos a haS b (by simp [LA, hab])
        rw [div_eq_mul_inv]
        simp only [one_mul]
        have hcast : ((S.filter fun a => r a b).card : ℚ) <=
            ((RB b).card : ℚ) := by exact_mod_cast hsub
        have hinv : 0 <= (((RB b).card : ℚ)⁻¹) := by positivity
        calc
          ((S.filter fun a => r a b).card : ℚ) *
              ((RB b).card : ℚ)⁻¹ <=
            ((RB b).card : ℚ) * ((RB b).card : ℚ)⁻¹ :=
              mul_le_mul_of_nonneg_right hcast hinv
          _ = 1 := by field_simp
      _ = (N.card : ℚ) := by simp
  have hrat : (S.card : ℚ) <= (N.card : ℚ) := by
    rw [hleft]
    exact hstep.trans (hreindex.le.trans hright)
  exact_mod_cast hrat




theorem tightBipartiteNeighborhood_collisionSurplus
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
    (htight : N.card + 1 = S.card) :
    (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card =
      (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card + 1 := by
  have hfilter : ∀ a ∈ S, N.filter (r a) = Finset.univ.filter (r a) := by
    intro a ha
    ext b
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun hab => ⟨⟨a, ha, hab⟩, hab⟩
  have hedge := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    r (s := S) (t := N)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hedge
  have hedgeNat : (∑ a ∈ S,
      (Finset.univ.filter (r a)).card) =
      ∑ b ∈ N, (S.filter fun a => r a b).card := by
    calc
      _ = ∑ a ∈ S, (N.filter (r a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfilter a ha]
      _ = _ := hedge
  have hedge' : (∑ a ∈ S,
      ((Finset.univ.filter (r a)).card : ℤ)) =
      ∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ) := by
    exact_mod_cast hedgeNat
  omega




theorem bipartiteNeighborhood_collisionSurplus
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b) :
    (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card =
      (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card +
        ((S.card : ℤ) - N.card) := by
  have hfilter : ∀ a ∈ S, N.filter (r a) =
      Finset.univ.filter (r a) := by
    intro a ha
    ext b
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun hab => ⟨⟨a, ha, hab⟩, hab⟩
  have hedge := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    r (s := S) (t := N)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hedge
  have hedgeNat : (∑ a ∈ S,
      (Finset.univ.filter (r a)).card) =
      ∑ b ∈ N, (S.filter fun a => r a b).card := by
    calc
      _ = ∑ a ∈ S, (N.filter (r a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfilter a ha]
      _ = _ := hedge
  have hedge' : (∑ a ∈ S,
      ((Finset.univ.filter (r a)).card : ℤ)) =
      ∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ) := by
    exact_mod_cast hedgeNat
  omega



theorem card_le_bipartiteNeighbors_of_collisionSurplus
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
    (hsurplus :
      (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card ≤
        (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card) :
    S.card ≤ N.card := by
  have hid := bipartiteNeighborhood_collisionSurplus r S N hN
  omega





theorem bipartiteNeighborhood_collisionSurplus_iff_card_le
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b) :
    ((∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card ≤
        (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card) ↔
      S.card ≤ N.card := by
  have hid := bipartiteNeighborhood_collisionSurplus r S N hN
  omega


noncomputable def bipartiteLeftSurplusToken
    [DecidableEq B] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (base : ↑S -> B) : Type _ :=
  Σ a : ↑S, ↑((Finset.univ.filter (r a.1)).erase (base a))


noncomputable def bipartiteRightCollisionToken
    [DecidableEq A] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (N : Finset B) (base : ↑N -> A) : Type _ :=
  Σ b : ↑N, ↑((S.filter fun a => r a b.1).erase (base b))

noncomputable instance instFintypeBipartiteLeftSurplusToken
    [DecidableEq B] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (base : ↑S -> B) :
    Fintype (bipartiteLeftSurplusToken r S base) := by
  unfold bipartiteLeftSurplusToken
  infer_instance

noncomputable instance instFintypeBipartiteRightCollisionToken
    [DecidableEq A] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (N : Finset B) (base : ↑N -> A) :
    Fintype (bipartiteRightCollisionToken r S N base) := by
  unfold bipartiteRightCollisionToken
  infer_instance



theorem bipartiteLeftSurplusToken_eq_of_source_target_eq
    [DecidableEq B] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (base : ↑S -> B)
    {x y : bipartiteLeftSurplusToken r S base}
    (hsource : x.1 = y.1) (htarget : x.2.1 = y.2.1) : x = y := by
  rcases x with ⟨xsource, xtarget, hx⟩
  rcases y with ⟨ysource, ytarget, hy⟩
  simp only at hsource htarget
  subst ysource
  subst ytarget
  rfl




theorem cycleCollisionAndSurplusTokenEmbeddings
    {C : Type*} [Fintype C]
    [DecidableEq A] [DecidableEq B]
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (N : Finset B)
    (leftBase : ↑S -> B) (rightBase : ↑N -> A)
    (σ : Equiv.Perm C) (source : C -> ↑S) (target : C -> ↑N)
    (hσ : ∀ x, σ x ≠ x)
    (htarget : Function.Injective target)
    (hsourceNext : ∀ x, source x ≠ source (σ x))
    (hcurrent : ∀ x, r (source x).1 (target x).1)
    (hnext : ∀ x, r (source x).1 (target (σ x)).1)
    (hexceptional : ∀ x, (source x).1 ≠ rightBase (target x)) :
    Nonempty (C ↪ bipartiteRightCollisionToken r S N rightBase) ∧
      Nonempty (C ↪ bipartiteLeftSurplusToken r S leftBase) := by
  classical
  have hrightMem (x : C) : (source x).1 ∈
      (S.filter fun a => r a (target x).1).erase (rightBase (target x)) := by
    apply Finset.mem_erase.mpr
    exact ⟨hexceptional x,
      Finset.mem_filter.mpr ⟨(source x).2, hcurrent x⟩⟩
  let rightToken : C -> bipartiteRightCollisionToken r S N rightBase :=
    fun x => ⟨target x, ⟨(source x).1, hrightMem x⟩⟩
  have hrightInjective : Function.Injective rightToken := by
    intro x y hxy
    apply htarget
    exact congrArg Sigma.fst hxy
  let outputTarget : C -> B := fun x =>
    if (target x).1 = leftBase (source x) then
      (target (σ x)).1 else (target x).1
  have houtputRelated (x : C) : r (source x).1 (outputTarget x) := by
    dsimp only [outputTarget]
    split
    · exact hnext x
    · exact hcurrent x
  have houtputNe (x : C) : outputTarget x ≠ leftBase (source x) := by
    dsimp only [outputTarget]
    split
    next heq =>
      intro hnextBase
      apply hσ x
      apply htarget
      apply Subtype.ext
      exact hnextBase.trans heq.symm
    next hne => exact hne
  have hleftMem (x : C) : outputTarget x ∈
      (Finset.univ.filter (r (source x).1)).erase (leftBase (source x)) := by
    apply Finset.mem_erase.mpr
    exact ⟨houtputNe x,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, houtputRelated x⟩⟩
  let leftToken : C -> bipartiteLeftSurplusToken r S leftBase :=
    fun x => ⟨source x, ⟨outputTarget x, hleftMem x⟩⟩
  have hleftInjective : Function.Injective leftToken := by
    intro x y hxy
    have hsourceEq : source x = source y := congrArg Sigma.fst hxy
    have htargetEq : outputTarget x = outputTarget y := by
      exact congrArg (fun z => z.2.1) hxy
    by_cases hx : (target x).1 = leftBase (source x)
    · by_cases hy : (target y).1 = leftBase (source y)
      · apply σ.injective
        apply htarget
        apply Subtype.ext
        simpa only [outputTarget, if_pos hx, if_pos hy] using htargetEq
      · have hindex : σ x = y := by
          apply htarget
          apply Subtype.ext
          simpa only [outputTarget, if_pos hx, if_neg hy] using htargetEq
        exfalso
        apply hsourceNext x
        rw [hindex]
        exact hsourceEq
    · by_cases hy : (target y).1 = leftBase (source y)
      · have hindex : x = σ y := by
          apply htarget
          apply Subtype.ext
          simpa only [outputTarget, if_neg hx, if_pos hy] using htargetEq
        exfalso
        apply hsourceNext y
        rw [← hindex]
        exact hsourceEq.symm
      · apply htarget
        apply Subtype.ext
        simpa only [outputTarget, if_neg hx, if_neg hy] using htargetEq
  exact ⟨⟨⟨rightToken, hrightInjective⟩⟩,
    ⟨⟨leftToken, hleftInjective⟩⟩⟩





def BipartiteCollisionTokenEmbedding
    [DecidableEq A] [DecidableEq B]
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (N : Finset B) : Prop :=
  ∃ (leftBase : ↑S -> B) (rightBase : ↑N -> A),
    (∀ a, r a.1 (leftBase a)) ∧
      (∀ b, rightBase b ∈ S ∧ r (rightBase b) b.1) ∧
      Nonempty
        (bipartiteRightCollisionToken r S N rightBase ↪
          bipartiteLeftSurplusToken r S leftBase)




theorem card_le_bipartiteNeighbors_of_collisionTokenEmbedding
    [DecidableEq A] [DecidableEq B]
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A)
    (N : Finset B)
    (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
    (hemb : BipartiteCollisionTokenEmbedding r S N) :
    S.card ≤ N.card := by
  classical
  obtain ⟨leftBase, rightBase, hleft, hright, ⟨f⟩⟩ := hemb
  have hleftMem (a : ↑S) :
      leftBase a ∈ Finset.univ.filter (r a.1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hleft a
  have hrightMem (b : ↑N) :
      rightBase b ∈ S.filter fun a => r a b.1 := by
    exact Finset.mem_filter.mpr (hright b)
  have hleftCard : Fintype.card
      (bipartiteLeftSurplusToken r S leftBase) + S.card =
      ∑ a ∈ S, (Finset.univ.filter (r a)).card := by
    calc
      _ = (∑ a : ↑S,
            ((Finset.univ.filter (r a.1)).card - 1)) + S.card := by
        congr 1
        calc
          _ = ∑ a : ↑S, Fintype.card
              ↑((Finset.univ.filter (r a.1)).erase (leftBase a)) :=
            Fintype.card_sigma
          _ = _ := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Fintype.card_coe,
              Finset.card_erase_of_mem (hleftMem a)]
      _ = (∑ a : ↑S,
            ((Finset.univ.filter (r a.1)).card - 1)) +
          ∑ _a : ↑S, 1 := by simp
      _ = ∑ a : ↑S,
          (((Finset.univ.filter (r a.1)).card - 1) + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ a : ↑S, (Finset.univ.filter (r a.1)).card := by
        apply Finset.sum_congr rfl
        intro a _
        have hpos := Finset.card_pos.mpr ⟨leftBase a, hleftMem a⟩
        omega
      _ = _ := Finset.sum_coe_sort S
        (fun a => (Finset.univ.filter (r a)).card)
  have hrightCard : Fintype.card
      (bipartiteRightCollisionToken r S N rightBase) + N.card =
      ∑ b ∈ N, (S.filter fun a => r a b).card := by
    calc
      _ = (∑ b : ↑N,
            ((S.filter fun a => r a b.1).card - 1)) + N.card := by
        congr 1
        calc
          _ = ∑ b : ↑N, Fintype.card
              ↑((S.filter fun a => r a b.1).erase (rightBase b)) :=
            Fintype.card_sigma
          _ = _ := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Fintype.card_coe,
              Finset.card_erase_of_mem (hrightMem b)]
      _ = (∑ b : ↑N,
            ((S.filter fun a => r a b.1).card - 1)) +
          ∑ _b : ↑N, 1 := by simp
      _ = ∑ b : ↑N,
          (((S.filter fun a => r a b.1).card - 1) + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ b : ↑N, (S.filter fun a => r a b.1).card := by
        apply Finset.sum_congr rfl
        intro b _
        have hpos := Finset.card_pos.mpr ⟨rightBase b, hrightMem b⟩
        omega
      _ = _ := Finset.sum_coe_sort N
        (fun b => (S.filter fun a => r a b).card)
  have htoken := Fintype.card_le_of_embedding f
  have hedge := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    r (s := S) (t := N)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hedge
  have hfilter : ∀ a ∈ S, N.filter (r a) =
      Finset.univ.filter (r a) := by
    intro a ha
    ext b
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun hab => ⟨⟨a, ha, hab⟩, hab⟩
  have hedge' : (∑ a ∈ S, (Finset.univ.filter (r a)).card) =
      ∑ b ∈ N, (S.filter fun a => r a b).card := by
    calc
      _ = ∑ a ∈ S, (N.filter (r a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hfilter a ha]
      _ = _ := hedge
  omega

end StatMech.FrontierA

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskRightLeftDegree
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) : Nat := by
  classical
  exact Fintype.card {q : rightMaskFiber ends m j k l zero p //
    q ∈ canonicalMaskRightImages ends m j k l zero p c}


noncomputable def canonicalMaskRightRightDegree
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q : rightMaskFiber ends m j k l zero p) : Nat := by
  classical
  exact Fintype.card {c : leftMaskFiber ends m j k l zero p //
    q ∈ canonicalMaskRightImages ends m j k l zero p c}


def CanonicalMaskRightEdgeDegreeDominance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c : leftMaskFiber ends m j k l zero p,
    ∀ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p c ->
        canonicalMaskRightRightDegree ends m j k l zero p q <=
          canonicalMaskRightLeftDegree ends m j k l zero p c




def CanonicalMaskRightEdgePreimageEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c : leftMaskFiber ends m j k l zero p,
    ∀ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p c ->
        Nonempty
          ({d : leftMaskFiber ends m j k l zero p //
              q ∈ canonicalMaskRightImages ends m j k l zero p d} ↪
            {r : rightMaskFiber ends m j k l zero p //
              r ∈ canonicalMaskRightImages ends m j k l zero p c})


theorem canonicalMaskRightEdgeDegreeDominance_of_preimageEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hemb : CanonicalMaskRightEdgePreimageEmbedding
      ends m j k l zero p) :
    CanonicalMaskRightEdgeDegreeDominance ends m j k l zero p := by
  classical
  intro c q hqc
  obtain ⟨f⟩ := hemb c q hqc
  have hcard := Fintype.card_le_of_embedding f
  simpa only [canonicalMaskRightRightDegree,
    canonicalMaskRightLeftDegree] using hcard



noncomputable def canonicalMaskRightPreimageReference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q : rightMaskFiber ends m j k l zero p)
    (d : {d : leftMaskFiber ends m j k l zero p //
      q ∈ canonicalMaskRightImages ends m j k l zero p d}) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose ((mem_canonicalMaskRightImages_iff
    ends m j k l zero p d.1 q).mp d.2)

theorem canonicalMaskRightPreimageReference_works
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q : rightMaskFiber ends m j k l zero p)
    (d : {d : leftMaskFiber ends m j k l zero p //
      q ∈ canonicalMaskRightImages ends m j k l zero p d}) :
    CanonicalTransferWorks ends m k zero
      (canonicalMaskRightPreimageReference
        ends m j k l zero p q d).1.1 d.1.1.1 :=
  (Classical.choose_spec ((mem_canonicalMaskRightImages_iff
    ends m j k l zero p d.1 q).mp d.2)).1

theorem canonicalMaskRightPreimageReference_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q : rightMaskFiber ends m j k l zero p)
    (d : {d : leftMaskFiber ends m j k l zero p //
      q ∈ canonicalMaskRightImages ends m j k l zero p d}) :
    q.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m
        (canonicalMaskRightPreimageReference
          ends m j k l zero p q d).1.1 k zero)
      (canonicalOuterTransfer ends m
        (canonicalMaskRightPreimageReference
          ends m j k l zero p q d).1.1 k zero) d.1.1.1 :=
  (Classical.choose_spec ((mem_canonicalMaskRightImages_iff
    ends m j k l zero p d.1 q).mp d.2)).2




def CanonicalMaskRightSelectedOppositeClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c : leftMaskFiber ends m j k l zero p,
    ∀ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p c ->
        ∀ d : {d : leftMaskFiber ends m j k l zero p //
          q ∈ canonicalMaskRightImages ends m j k l zero p d},
          CanonicalTransferWorks ends m k zero
            (canonicalMaskRightPreimageReference
              ends m j k l zero p q d).1.1 c.1.1



noncomputable def canonicalMaskRightEdgePreimageEmbedding_of_selectedOppositeClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hclose : CanonicalMaskRightSelectedOppositeClosure
      ends m j k l zero p) :
    CanonicalMaskRightEdgePreimageEmbedding ends m j k l zero p := by
  intro c q hqc
  let source := {d : leftMaskFiber ends m j k l zero p //
    q ∈ canonicalMaskRightImages ends m j k l zero p d}
  let target := {r : rightMaskFiber ends m j k l zero p //
    r ∈ canonicalMaskRightImages ends m j k l zero p c}
  let ref : source -> leftMaskFiber ends m j k l zero p := fun d =>
    canonicalMaskRightPreimageReference ends m j k l zero p q d
  let works : ∀ d : source,
      CanonicalTransferWorks ends m k zero (ref d).1.1 c.1.1 := fun d =>
    hclose c q hqc d
  let f : source -> target := fun d =>
    ⟨canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p (ref d) c (works d),
      (mem_canonicalMaskRightImages_iff
        ends m j k l zero p c _).mpr ⟨ref d, works d, rfl⟩⟩
  refine ⟨⟨f, ?_⟩⟩
  intro d e hde
  have hrawC := congrArg (fun z : target => z.1.1.1) hde
  have hrowC := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl (ref d) (ref e) c c).mp hrawC
  have htransfer : canonicalTransferUnion ends m k zero (ref d).1.1 =
      canonicalTransferUnion ends m k zero (ref e).1.1 := by
    have h := congrArg (fun K : Finset I =>
      (rowClass m c.1.1 0) ∆ K) hrowC
    simpa [symmDiff_assoc] using h
  have hrawD : balancedSwap m
        (canonicalMiddleTransfer ends m (ref d).1.1 k zero)
        (canonicalOuterTransfer ends m (ref d).1.1 k zero) d.1.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m (ref e).1.1 k zero)
        (canonicalOuterTransfer ends m (ref e).1.1 k zero) e.1.1.1 :=
    (canonicalMaskRightPreimageReference_eq
      ends m j k l zero p q d).symm.trans
        (canonicalMaskRightPreimageReference_eq
          ends m j k l zero p q e)
  have hrowD := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl (ref d) (ref e) d.1 e.1).mp hrawD
  rw [htransfer] at hrowD
  have hsupport : rowClass m d.1.1.1 0 = rowClass m e.1.1.1 0 := by
    have h := congrArg (fun K : Finset I =>
      K ∆ (canonicalTransferUnion ends m k zero (ref e).1.1)) hrowD
    simpa [symmDiff_assoc] using h
  apply Subtype.ext
  exact leftMaskFiber_rowClass_zero_injective
    ends m j k l zero p hsupport



theorem canonicalMaskRightEdgeDegreeDominance_of_selectedOppositeClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hclose : CanonicalMaskRightSelectedOppositeClosure
      ends m j k l zero p) :
    CanonicalMaskRightEdgeDegreeDominance ends m j k l zero p :=
  canonicalMaskRightEdgeDegreeDominance_of_preimageEmbedding
    ends m j k l zero p
      (canonicalMaskRightEdgePreimageEmbedding_of_selectedOppositeClosure
        ends m j k l zero hloop hjk hkl p hclose)

end StatMech.GrahamGHS.FourColor
