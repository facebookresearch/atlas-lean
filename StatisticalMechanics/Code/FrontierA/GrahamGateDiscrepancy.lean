/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max










namespace StatMech.FrontierA



theorem card_subtype_le_iff_card_leftOnly_le_card_rightOnly
    {A : Type*} [Fintype A] (P Q : A -> Prop)
    [DecidablePred P] [DecidablePred Q] :
    Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} ↔
      Fintype.card {a : A // P a ∧ ¬ Q a} <=
        Fintype.card {a : A // ¬ P a ∧ Q a} := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype,
    Fintype.card_subtype, Fintype.card_subtype]
  let s := Finset.univ.filter P
  let t := Finset.univ.filter Q
  have hleft :
      Finset.univ.filter (fun a => P a ∧ ¬ Q a) = s \ t := by
    ext a
    simp [s, t]
  have hright :
      Finset.univ.filter (fun a => ¬ P a ∧ Q a) = t \ s := by
    ext a
    simp [s, t, and_comm]
  rw [hleft, hright]
  change s.card <= t.card ↔ (s \ t).card <= (t \ s).card
  have hs := Finset.card_sdiff_add_card s t
  have ht := Finset.card_sdiff_add_card t s
  rw [Finset.union_comm t s] at ht
  omega



theorem card_subtype_le_of_discrepancyEmbedding
    {A : Type*} [Fintype A] (P Q : A -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (f : {a : A // P a ∧ ¬ Q a} ↪ {a : A // ¬ P a ∧ Q a}) :
    Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} := by
  rw [card_subtype_le_iff_card_leftOnly_le_card_rightOnly P Q]
  exact Fintype.card_le_of_injective f f.injective




def embeddingOf_tag_preserving_fiberwise
    {B C S : Type*} (sourceTag : B -> S) (targetTag : C -> S)
    (f : B -> C)
    (htag : ∀ x, targetTag (f x) = sourceTag x)
    (hfiber : ∀ s, Function.Injective fun x : {x : B // sourceTag x = s} =>
      f x.1) : B ↪ C where
  toFun := f
  inj' := by
    intro x y hxy
    have htags : sourceTag x = sourceTag y := by
      rw [← htag x, ← htag y, hxy]
    let xs : {z : B // sourceTag z = sourceTag x} := ⟨x, rfl⟩
    let ys : {z : B // sourceTag z = sourceTag x} := ⟨y, htags.symm⟩
    have hsub : xs = ys := hfiber (sourceTag x) (by
      change f x = f y
      exact hxy)
    exact congrArg Subtype.val hsub





def embeddingOf_taggedFiberwiseMaps
    {B C S : Type*} (sourceTag : B -> S) (targetTag : C -> S)
    (f : S -> B -> C)
    (htag : ∀ s x, sourceTag x = s -> targetTag (f s x) = s)
    (hinj : ∀ s, Function.Injective fun
      x : {x : B // sourceTag x = s} => f s x.1) : B ↪ C := by
  let assembled : B -> C := fun x => f (sourceTag x) x
  apply embeddingOf_tag_preserving_fiberwise
    sourceTag targetTag assembled
  · intro x
    exact htag (sourceTag x) x rfl
  · intro s x y hxy
    have hsub : x = y := hinj s (by
      simpa only [assembled, x.2, y.2] using hxy)
    exact hsub




noncomputable def embeddingOf_taggedFiberwiseCardLE
    {B C S : Type*} [Fintype B] [Fintype C] [DecidableEq S]
    (sourceTag : B -> S) (targetTag : C -> S)
    (hcard : ∀ s,
      Fintype.card {x : B // sourceTag x = s} ≤
        Fintype.card {y : C // targetTag y = s}) : B ↪ C := by
  classical
  let fibreEmbedding : ∀ s,
      {x : B // sourceTag x = s} ↪ {y : C // targetTag y = s} :=
    fun s => Classical.choice (Function.Embedding.nonempty_of_card_le (hcard s))
  by_cases hB : Nonempty B
  · let x : B := Classical.choice hB
    let c : C := (fibreEmbedding (sourceTag x) ⟨x, rfl⟩).1
    let f : S -> B -> C := fun s y =>
      if h : sourceTag y = s then (fibreEmbedding s ⟨y, h⟩).1 else c
    apply embeddingOf_taggedFiberwiseMaps sourceTag targetTag f
    · intro s y hy
      simp only [f, dif_pos hy]
      exact (fibreEmbedding s ⟨y, hy⟩).2
    · intro s y z hyz
      apply (fibreEmbedding s).injective
      apply Subtype.ext
      simpa only [f, dif_pos y.2, dif_pos z.2] using hyz
  · exact ⟨fun x => False.elim (hB ⟨x⟩), fun x => False.elim (hB ⟨x⟩)⟩




def functionWeakComponent {B : Type*} (next : B -> B) (x : B) : Set B :=
  {y | Relation.EqvGen (fun a b => next a = b) x y}

@[simp] theorem mem_functionWeakComponent_self
    {B : Type*} (next : B -> B) (x : B) :
    x ∈ functionWeakComponent next x :=
  Relation.EqvGen.refl x

theorem functionWeakComponent_eq_of_mem
    {B : Type*} (next : B -> B) {x y : B}
    (hxy : y ∈ functionWeakComponent next x) :
    functionWeakComponent next x = functionWeakComponent next y := by
  ext z
  constructor
  · intro hxz
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ hxy) hxz
  · intro hyz
    exact Relation.EqvGen.trans _ _ _ hxy hyz

@[simp] theorem functionWeakComponent_next
    {B : Type*} (next : B -> B) (x : B) :
    functionWeakComponent next (next x) = functionWeakComponent next x := by
  symm
  apply functionWeakComponent_eq_of_mem
  exact Relation.EqvGen.rel x (next x) rfl



def embeddingOf_functionWeakComponentwiseMaps
    {B C : Type*} (next : B -> B) (targetComponent : C -> Set B)
    (f : Set B -> B -> C)
    (htag : ∀ component x, functionWeakComponent next x = component ->
      targetComponent (f component x) = component)
    (hinj : ∀ component, Function.Injective fun
      x : {x : B // functionWeakComponent next x = component} =>
        f component x.1) : B ↪ C :=
  embeddingOf_taggedFiberwiseMaps
    (functionWeakComponent next) targetComponent f htag hinj


def crossCollision {A B C : Type*} (f : A -> C) (g : B -> C) :=
  {pair : A × B // f pair.1 = g pair.2}

theorem crossCollision_fst_injective
    {A B C : Type*} (f : A ↪ C) (g : B ↪ C) :
    Function.Injective fun collision : crossCollision f g => collision.1.1 := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext hxy
  apply g.injective
  calc
    g x.1.2 = f x.1.1 := x.2.symm
    _ = f y.1.1 := congrArg f hxy
    _ = g y.1.2 := y.2

theorem crossCollision_snd_injective
    {A B C : Type*} (f : A ↪ C) (g : B ↪ C) :
    Function.Injective fun collision : crossCollision f g => collision.1.2 := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · apply f.injective
    calc
      f x.1.1 = g x.1.2 := x.2
      _ = g y.1.2 := congrArg g hxy
      _ = f y.1.1 := y.2.symm
  · exact hxy



noncomputable def embeddingSumOfCrossCollisionCharge
    {A B C : Type*} (f : A ↪ C) (g : B ↪ C)
    (charge : crossCollision f g ↪ C)
    (hfreshLeft : ∀ collision a, charge collision ≠ f a)
    (hfreshRight : ∀ collision b, charge collision ≠ g b) :
    A ⊕ B ↪ C := by
  classical
  let hasCollision := fun b : B => ∃ a : A, f a = g b
  let chosenCollision (b : B) (h : hasCollision b) : crossCollision f g :=
    ⟨(Classical.choose h, b), Classical.choose_spec h⟩
  let merged : A ⊕ B -> C
    | Sum.inl a => f a
    | Sum.inr b => if h : hasCollision b then charge (chosenCollision b h)
        else g b
  refine ⟨merged, ?_⟩
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          simp only [merged, f.injective.eq_iff] at hxy
          exact congrArg Sum.inl hxy
      | inr b =>
          by_cases hb : hasCollision b
          · simp only [merged, dif_pos hb] at hxy
            exact False.elim (hfreshLeft (chosenCollision b hb) a hxy.symm)
          · simp only [merged, dif_neg hb] at hxy
            exact False.elim (hb ⟨a, hxy⟩)
  | inr b =>
      cases y with
      | inl a =>
          by_cases hb : hasCollision b
          · simp only [merged, dif_pos hb] at hxy
            exact False.elim (hfreshLeft (chosenCollision b hb) a hxy)
          · simp only [merged, dif_neg hb] at hxy
            exact False.elim (hb ⟨a, hxy.symm⟩)
      | inr b' =>
          by_cases hb : hasCollision b
          · by_cases hb' : hasCollision b'
            · simp only [merged, dif_pos hb, dif_pos hb'] at hxy
              have hcollision := charge.injective hxy
              have hpair := congrArg Subtype.val hcollision
              exact congrArg Sum.inr (congrArg Prod.snd hpair)
            · simp only [merged, dif_pos hb, dif_neg hb'] at hxy
              exact False.elim
                (hfreshRight (chosenCollision b hb) b' hxy)
          · by_cases hb' : hasCollision b'
            · simp only [merged, dif_neg hb, dif_pos hb'] at hxy
              exact False.elim
                (hfreshRight (chosenCollision b' hb') b hxy.symm)
            · simp only [merged, dif_neg hb, dif_neg hb'] at hxy
              exact congrArg Sum.inr (g.injective hxy)




noncomputable def embeddingSumOfCrossCollisionSecondCharge
    {A B C : Type*} (f : A ↪ C) (g : B ↪ C)
    (first : crossCollision f g ↪ C)
    (hfirstFreshLeft : ∀ collision a, first collision ≠ f a)
    (second : crossCollision first g ↪ C)
    (hsecondFreshLeft : ∀ collision a, second collision ≠ f a)
    (hsecondFreshRight : ∀ collision b, second collision ≠ g b)
    (hsecondFreshFirst : ∀ collision old, second collision ≠ first old) :
    A ⊕ B ↪ C := by
  classical
  let hasFirst := fun b : B => ∃ a : A, f a = g b
  let chosenFirst (b : B) (h : hasFirst b) : crossCollision f g :=
    ⟨(Classical.choose h, b), Classical.choose_spec h⟩
  let hasSecond := fun b : B => ∃ old : crossCollision f g, first old = g b
  let chosenSecond (b : B) (h : hasSecond b) : crossCollision first g :=
    ⟨(Classical.choose h, b), Classical.choose_spec h⟩
  let merged : A ⊕ B -> C
    | Sum.inl a => f a
    | Sum.inr b => if h₁ : hasFirst b then first (chosenFirst b h₁)
        else if h₂ : hasSecond b then second (chosenSecond b h₂) else g b
  refine ⟨merged, ?_⟩
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl a' =>
          simp only [merged, f.injective.eq_iff] at hxy
          exact congrArg Sum.inl hxy
      | inr b =>
          by_cases h₁ : hasFirst b
          · simp only [merged, dif_pos h₁] at hxy
            exact False.elim
              (hfirstFreshLeft (chosenFirst b h₁) a hxy.symm)
          · by_cases h₂ : hasSecond b
            · simp only [merged, dif_neg h₁, dif_pos h₂] at hxy
              exact False.elim
                (hsecondFreshLeft (chosenSecond b h₂) a hxy.symm)
            · simp only [merged, dif_neg h₁, dif_neg h₂] at hxy
              exact False.elim (h₁ ⟨a, hxy⟩)
  | inr b =>
      cases y with
      | inl a =>
          by_cases h₁ : hasFirst b
          · simp only [merged, dif_pos h₁] at hxy
            exact False.elim (hfirstFreshLeft (chosenFirst b h₁) a hxy)
          · by_cases h₂ : hasSecond b
            · simp only [merged, dif_neg h₁, dif_pos h₂] at hxy
              exact False.elim
                (hsecondFreshLeft (chosenSecond b h₂) a hxy)
            · simp only [merged, dif_neg h₁, dif_neg h₂] at hxy
              exact False.elim (h₁ ⟨a, hxy.symm⟩)
      | inr b' =>
          by_cases h₁ : hasFirst b
          · by_cases h₁' : hasFirst b'
            · simp only [merged, dif_pos h₁, dif_pos h₁'] at hxy
              have hc := first.injective hxy
              exact congrArg Sum.inr (congrArg (fun z => z.1.2) hc)
            · by_cases h₂' : hasSecond b'
              · simp only [merged, dif_pos h₁, dif_neg h₁',
                  dif_pos h₂'] at hxy
                exact False.elim
                  (hsecondFreshFirst (chosenSecond b' h₂')
                    (chosenFirst b h₁) hxy.symm)
              · simp only [merged, dif_pos h₁, dif_neg h₁',
                  dif_neg h₂'] at hxy
                exact False.elim (h₂' ⟨chosenFirst b h₁, hxy⟩)
          · by_cases h₁' : hasFirst b'
            · by_cases h₂ : hasSecond b
              · simp only [merged, dif_neg h₁, dif_pos h₂,
                  dif_pos h₁'] at hxy
                exact False.elim
                  (hsecondFreshFirst (chosenSecond b h₂)
                    (chosenFirst b' h₁') hxy)
              · simp only [merged, dif_neg h₁, dif_neg h₂,
                  dif_pos h₁'] at hxy
                exact False.elim (h₂ ⟨chosenFirst b' h₁', hxy.symm⟩)
            · by_cases h₂ : hasSecond b
              · by_cases h₂' : hasSecond b'
                · simp only [merged, dif_neg h₁, dif_pos h₂,
                    dif_neg h₁', dif_pos h₂'] at hxy
                  have hc := second.injective hxy
                  exact congrArg Sum.inr (congrArg (fun z => z.1.2) hc)
                · simp only [merged, dif_neg h₁, dif_pos h₂,
                    dif_neg h₁', dif_neg h₂'] at hxy
                  exact False.elim
                    (hsecondFreshRight (chosenSecond b h₂) b' hxy)
              · by_cases h₂' : hasSecond b'
                · simp only [merged, dif_neg h₁, dif_neg h₂,
                    dif_neg h₁', dif_pos h₂'] at hxy
                  exact False.elim
                    (hsecondFreshRight (chosenSecond b' h₂') b hxy.symm)
                · simp only [merged, dif_neg h₁, dif_neg h₂,
                    dif_neg h₁', dif_neg h₂'] at hxy
                  exact congrArg Sum.inr (g.injective hxy)




theorem exists_secondCollisionCharge_of_card_le
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A ↪ C) (g : B ↪ C)
    (first : crossCollision f g ↪ C)
    (hfirstFreshLeft : ∀ collision a, first collision ≠ f a)
    (hcard : Fintype.card A + Fintype.card B ≤ Fintype.card C) :
    ∃ second : crossCollision first g ↪ C,
      (∀ collision a, second collision ≠ f a) ∧
      (∀ collision b, second collision ≠ g b) ∧
      ∀ collision old, second collision ≠ first old := by
  classical
  letI : Fintype (crossCollision f g) :=
    Fintype.ofInjective (fun collision => collision.1.1)
      (crossCollision_fst_injective f g)
  letI : Fintype (crossCollision first g) :=
    Fintype.ofInjective (fun collision => collision.1.1)
      (crossCollision_fst_injective first g)
  let F : Finset C := Finset.univ.map f
  let G : Finset C := Finset.univ.map g
  let H : Finset C := Finset.univ.map first
  let fgValue : crossCollision f g ↪ C :=
    ⟨fun collision => f collision.1.1, fun x y h =>
      crossCollision_fst_injective f g (f.injective h)⟩
  let hgValue : crossCollision first g ↪ C :=
    ⟨fun collision => first collision.1.1, fun x y h =>
      crossCollision_fst_injective first g (first.injective h)⟩
  have hFG : F ∩ G = Finset.univ.map fgValue := by
    ext c
    simp only [F, G, Finset.mem_inter, Finset.mem_map, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hab⟩⟩
      exact ⟨⟨(a, b), hab.symm⟩, rfl⟩
    · rintro ⟨collision, rfl⟩
      exact ⟨⟨collision.1.1, rfl⟩,
        ⟨collision.1.2, collision.2.symm⟩⟩
  have hFH : F ∩ H = ∅ := by
    ext c
    constructor
    · rintro hc
      obtain ⟨⟨a, ha⟩, ⟨collision, hcollision⟩⟩ := by
        simpa only [F, H, Finset.mem_inter, Finset.mem_map,
          Finset.mem_univ, true_and] using hc
      exact False.elim (hfirstFreshLeft collision a
        (hcollision.trans ha.symm))
    · simp
  have hGH : G ∩ H = Finset.univ.map hgValue := by
    ext c
    simp only [G, H, Finset.mem_inter, Finset.mem_map, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨b, rfl⟩, ⟨old, hold⟩⟩
      exact ⟨⟨(old, b), hold⟩, hold⟩
    · rintro ⟨collision, rfl⟩
      exact ⟨⟨collision.1.2, collision.2.symm⟩,
        ⟨collision.1.1, rfl⟩⟩
  have hUnionInter : (F ∪ G) ∩ H = G ∩ H := by
    ext c
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hFGc, hcH⟩
      rcases hFGc with hcF | hcG
      · exact False.elim (by
          have : c ∈ F ∩ H := Finset.mem_inter.mpr ⟨hcF, hcH⟩
          simpa [hFH] using this)
      · exact ⟨hcG, hcH⟩
    · rintro ⟨hcG, hcH⟩
      exact ⟨Or.inr hcG, hcH⟩
  have hFcard : F.card = Fintype.card A := by simp [F]
  have hGcard : G.card = Fintype.card B := by simp [G]
  have hHcard : H.card = Fintype.card (crossCollision f g) := by simp [H]
  have hFGcard : (F ∩ G).card = Fintype.card (crossCollision f g) := by
    rw [hFG]
    simp
  have hGHcard : (G ∩ H).card =
      Fintype.card (crossCollision first g) := by
    rw [hGH]
    simp
  have hUnionCard : (F ∪ G ∪ H).card +
      Fintype.card (crossCollision first g) =
      Fintype.card A + Fintype.card B := by
    have hFGunion := Finset.card_union_add_card_inter F G
    have hFGHunion := Finset.card_union_add_card_inter (F ∪ G) H
    rw [hFcard, hGcard, hFGcard] at hFGunion
    rw [hUnionInter, hGHcard, hHcard] at hFGHunion
    omega
  let available : Finset C := Finset.univ \ (F ∪ G ∪ H)
  have hAvailableCard : Fintype.card (crossCollision first g) ≤
      available.card := by
    have hsubset : F ∪ G ∪ H ⊆ (Finset.univ : Finset C) := by
      exact fun _ _ => Finset.mem_univ _
    have hsub := Finset.card_sdiff_of_subset hsubset
    change available.card = Fintype.card C - (F ∪ G ∪ H).card at hsub
    omega
  let intoAvailable : crossCollision first g ↪ ↑available :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe] using hAvailableCard))
  let second : crossCollision first g ↪ C :=
    intoAvailable.trans ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨second, ?_, ?_, ?_⟩
  · intro collision a heq
    have havail := (intoAvailable collision).2
    have hnotUnion := (Finset.mem_sdiff.mp havail).2
    apply hnotUnion
    apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_union.mpr
    apply Or.inl
    simpa only [F, Finset.mem_map, Finset.mem_univ, true_and, second] using
      ⟨a, heq.symm⟩
  · intro collision b heq
    have havail := (intoAvailable collision).2
    have hnotUnion := (Finset.mem_sdiff.mp havail).2
    apply hnotUnion
    apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_union.mpr
    apply Or.inr
    simpa only [G, Finset.mem_map, Finset.mem_univ, true_and, second] using
      ⟨b, heq.symm⟩
  · intro collision old heq
    have havail := (intoAvailable collision).2
    have hnotUnion := (Finset.mem_sdiff.mp havail).2
    apply hnotUnion
    apply Finset.mem_union.mpr
    apply Or.inr
    simpa only [H, Finset.mem_map, Finset.mem_univ, true_and, second] using
      ⟨old, heq.symm⟩



structure RelationPartialMatching {A B : Type*} (r : A -> B -> Prop) where
  toFun : A -> Option B
  related : ∀ {a b}, toFun a = some b -> r a b
  injective_some : ∀ {a₁ a₂ b},
    toFun a₁ = some b -> toFun a₂ = some b -> a₁ = a₂

noncomputable instance instFintypeRelationPartialMatching
    {A B : Type*} [Fintype A] [Fintype B] (r : A -> B -> Prop) :
    Fintype (RelationPartialMatching r) := by
  classical
  let encode : RelationPartialMatching r -> A -> Option B :=
    fun matching => matching.toFun
  apply Fintype.ofInjective encode
  intro x y h
  cases x
  cases y
  cases h
  rfl


noncomputable def RelationPartialMatching.support
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) : Finset A := by
  classical
  exact Finset.univ.filter fun a => (matching.toFun a).isSome

@[simp] theorem RelationPartialMatching.mem_support_iff
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (a : A) :
    a ∈ matching.support ↔ ∃ b, matching.toFun a = some b := by
  classical
  simp only [RelationPartialMatching.support, Finset.mem_filter,
    Finset.mem_univ, true_and, Option.isSome_iff_exists]



def RelationPartialMatching.IsMaximum
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) : Prop :=
  ∀ other : RelationPartialMatching r,
    other.support.card ≤ matching.support.card


theorem exists_maximum_relationPartialMatching
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A -> B -> Prop) :
    ∃ matching : RelationPartialMatching r, matching.IsMaximum := by
  classical
  let candidates : Finset (RelationPartialMatching r) := Finset.univ
  have hcandidates : candidates.Nonempty := by
    let emptyMatching : RelationPartialMatching r :=
      ⟨fun _ => none, by simp, by simp⟩
    exact ⟨emptyMatching, by simp [candidates]⟩
  obtain ⟨matching, _hmem, hmax⟩ := candidates.exists_max_image
    (fun candidate => candidate.support.card) hcandidates
  exact ⟨matching, fun other => hmax other (by simp [candidates])⟩




theorem exists_relationPartialMatching_saturating_unmatched
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A -> B -> Prop) :
    ∃ matching : RelationPartialMatching r,
      matching.IsMaximum ∧
        ∀ a, a ∉ matching.support -> ∀ b, r a b ->
          ∃ a', matching.toFun a' = some b := by
  classical
  let candidates : Finset (RelationPartialMatching r) := Finset.univ
  have hcandidates : candidates.Nonempty := by
    let emptyMatching : RelationPartialMatching r :=
      ⟨fun _ => none, by simp, by simp⟩
    exact ⟨emptyMatching, by simp [candidates]⟩
  obtain ⟨matching, _hmem, hmax⟩ := candidates.exists_max_image
    (fun candidate => candidate.support.card) hcandidates
  refine ⟨matching, fun other => hmax other (by simp [candidates]), ?_⟩
  intro a ha b hab
  by_contra hunused
  push Not at hunused
  let extendedFun : A -> Option B := fun x =>
    if x = a then some b else matching.toFun x
  have hextendedRelated : ∀ {x y}, extendedFun x = some y -> r x y := by
    intro x y hxy
    by_cases hx : x = a
    · subst x
      simp only [extendedFun, if_pos] at hxy
      exact Option.some.inj hxy ▸ hab
    · simp only [extendedFun, if_neg hx] at hxy
      exact matching.related hxy
  have hextendedInjective : ∀ {x y z},
      extendedFun x = some z -> extendedFun y = some z -> x = y := by
    intro x y z hx hy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      · simp only [extendedFun, if_pos, Option.some.injEq] at hx
        simp only [extendedFun, if_neg hya] at hy
        exact False.elim (hunused y (hy.trans (congrArg some hx.symm)))
    · by_cases hya : y = a
      · subst y
        simp only [extendedFun, if_neg hxa] at hx
        simp only [extendedFun, if_pos, Option.some.injEq] at hy
        exact False.elim (hunused x (hx.trans (congrArg some hy.symm)))
      · simp only [extendedFun, if_neg hxa] at hx
        simp only [extendedFun, if_neg hya] at hy
        exact matching.injective_some hx hy
  let extended : RelationPartialMatching r :=
    ⟨extendedFun, hextendedRelated, hextendedInjective⟩
  have hsupport : extended.support = insert a matching.support := by
    ext x
    by_cases hx : x = a
    · subst x
      simp [RelationPartialMatching.mem_support_iff, extended, extendedFun]
    · simp [RelationPartialMatching.mem_support_iff, extended, extendedFun, hx]
  have hcard : extended.support.card = matching.support.card + 1 := by
    rw [hsupport, Finset.card_insert_of_notMem ha]
  have hle := hmax extended (by simp [candidates])
  omega




noncomputable def RelationPartialMatching.reassign
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) : RelationPartialMatching r := by
  classical
  let reassignedFun : A -> Option B := fun x =>
    if x = new then some b else if x = old then none else matching.toFun x
  refine ⟨reassignedFun, ?_, ?_⟩
  · intro x y hxy
    by_cases hxNew : x = new
    · subst x
      simp only [reassignedFun, if_pos, Option.some.injEq] at hxy
      exact hxy ▸ hnew
    · by_cases hxOld : x = old
      · subst x
        simp only [reassignedFun, if_neg hne.symm, if_pos] at hxy
        contradiction
      · simp only [reassignedFun, if_neg hxNew, if_neg hxOld] at hxy
        exact matching.related hxy
  · intro x y z hx hy
    by_cases hxNew : x = new
    · subst x
      by_cases hyNew : y = new
      · exact hyNew.symm
      · by_cases hyOld : y = old
        · subst y
          simp only [reassignedFun, if_neg hne.symm, if_pos] at hy
          contradiction
        · simp only [reassignedFun, if_pos, Option.some.injEq] at hx
          simp only [reassignedFun, if_neg hyNew, if_neg hyOld] at hy
          have hyEqOld := matching.injective_some
            (hy.trans (congrArg some hx.symm)) hold
          exact False.elim (hyOld hyEqOld)
    · by_cases hxOld : x = old
      · subst x
        simp only [reassignedFun, if_neg hne.symm, if_pos] at hx
        contradiction
      · by_cases hyNew : y = new
        · subst y
          simp only [reassignedFun, if_neg hxNew, if_neg hxOld] at hx
          simp only [reassignedFun, if_pos, Option.some.injEq] at hy
          have hxEqOld := matching.injective_some
            (hx.trans (congrArg some hy.symm)) hold
          exact False.elim (hxOld hxEqOld)
        · by_cases hyOld : y = old
          · subst y
            simp only [reassignedFun, if_neg hne.symm, if_pos] at hy
            contradiction
          · simp only [reassignedFun, if_neg hxNew, if_neg hxOld] at hx
            simp only [reassignedFun, if_neg hyNew, if_neg hyOld] at hy
            exact matching.injective_some hx hy

@[simp] theorem RelationPartialMatching.reassign_apply_new
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) :
    (matching.reassign new old b hne hold hnew).toFun new = some b := by
  classical
  simp [RelationPartialMatching.reassign]

@[simp] theorem RelationPartialMatching.reassign_apply_old
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) :
    (matching.reassign new old b hne hold hnew).toFun old = none := by
  classical
  simp [RelationPartialMatching.reassign, hne.symm]

theorem RelationPartialMatching.reassign_apply_of_ne
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old x : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) (hxNew : x ≠ new) (hxOld : x ≠ old) :
    (matching.reassign new old b hne hold hnew).toFun x = matching.toFun x := by
  classical
  simp [RelationPartialMatching.reassign, hxNew, hxOld]


theorem RelationPartialMatching.support_reassign
    {A B : Type*} [Fintype A] [DecidableEq A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) :
    (matching.reassign new old b hne hold hnew).support =
      insert new (matching.support.erase old) := by
  classical
  ext x
  by_cases hxNew : x = new
  · subst x
    simp [RelationPartialMatching.mem_support_iff]
  · by_cases hxOld : x = old
    · subst x
      simp [RelationPartialMatching.mem_support_iff, hne.symm]
    · simp [RelationPartialMatching.mem_support_iff,
        RelationPartialMatching.reassign_apply_of_ne,
        hxNew, hxOld]



theorem RelationPartialMatching.ne_of_not_mem_support_of_eq_some
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hnewUnmatched : new ∉ matching.support)
    (hold : matching.toFun old = some b) : new ≠ old := by
  intro h
  subst old
  exact hnewUnmatched
    ((RelationPartialMatching.mem_support_iff matching new).2 ⟨b, hold⟩)



theorem RelationPartialMatching.card_support_reassign
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hnewUnmatched : new ∉ matching.support)
    (hold : matching.toFun old = some b) (hnew : r new b) :
    (matching.reassign new old b
      (matching.ne_of_not_mem_support_of_eq_some
        new old b hnewUnmatched hold)
      hold hnew).support.card = matching.support.card := by
  classical
  let hne : new ≠ old := matching.ne_of_not_mem_support_of_eq_some
    new old b hnewUnmatched hold
  have holdMem : old ∈ matching.support :=
    (RelationPartialMatching.mem_support_iff matching old).2 ⟨b, hold⟩
  have hcardPositive : 0 < matching.support.card :=
    Finset.card_pos.mpr ⟨old, holdMem⟩
  have hnewErase : new ∉ matching.support.erase old := by
    simp only [Finset.mem_erase, not_and_or]
    exact Or.inr hnewUnmatched
  rw [RelationPartialMatching.support_reassign]
  rw [Finset.card_insert_of_notMem hnewErase,
    Finset.card_erase_of_mem holdMem]
  omega



theorem RelationPartialMatching.IsMaximum.reassign
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    {matching : RelationPartialMatching r} (hmaximum : matching.IsMaximum)
    (new old : A) (b : B) (hnewUnmatched : new ∉ matching.support)
    (hold : matching.toFun old = some b) (hnew : r new b) :
    (matching.reassign new old b
      (matching.ne_of_not_mem_support_of_eq_some
        new old b hnewUnmatched hold)
      hold hnew).IsMaximum := by
  intro other
  rw [RelationPartialMatching.card_support_reassign
    matching new old b hnewUnmatched hold hnew]
  exact hmaximum other




theorem RelationPartialMatching.IsMaximum.saturates_target_of_unmatched
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    {matching : RelationPartialMatching r} (hmaximum : matching.IsMaximum)
    (a : A) (ha : a ∉ matching.support) (b : B) (hab : r a b) :
    ∃ a', matching.toFun a' = some b := by
  classical
  by_contra hunused
  push Not at hunused
  let extendedFun : A -> Option B := fun x =>
    if x = a then some b else matching.toFun x
  have hextendedRelated : ∀ {x y}, extendedFun x = some y -> r x y := by
    intro x y hxy
    by_cases hx : x = a
    · subst x
      simp only [extendedFun, if_pos] at hxy
      exact Option.some.inj hxy ▸ hab
    · simp only [extendedFun, if_neg hx] at hxy
      exact matching.related hxy
  have hextendedInjective : ∀ {x y z},
      extendedFun x = some z -> extendedFun y = some z -> x = y := by
    intro x y z hx hy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      · simp only [extendedFun, if_pos, Option.some.injEq] at hx
        simp only [extendedFun, if_neg hya] at hy
        exact False.elim (hunused y (hy.trans (congrArg some hx.symm)))
    · by_cases hya : y = a
      · subst y
        simp only [extendedFun, if_neg hxa] at hx
        simp only [extendedFun, if_pos, Option.some.injEq] at hy
        exact False.elim (hunused x (hx.trans (congrArg some hy.symm)))
      · simp only [extendedFun, if_neg hxa] at hx
        simp only [extendedFun, if_neg hya] at hy
        exact matching.injective_some hx hy
  let extended : RelationPartialMatching r :=
    ⟨extendedFun, hextendedRelated, hextendedInjective⟩
  have hsupport : extended.support = insert a matching.support := by
    ext x
    by_cases hx : x = a
    · subst x
      simp [RelationPartialMatching.mem_support_iff, extended, extendedFun]
    · simp [RelationPartialMatching.mem_support_iff, extended, extendedFun, hx]
  have hcard : extended.support.card = matching.support.card + 1 := by
    rw [hsupport, Finset.card_insert_of_notMem ha]
  have hle := hmaximum extended
  omega


theorem RelationPartialMatching.card_support_le_target
    {A B : Type*} [Fintype A] [Fintype B] {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) :
    matching.support.card ≤ Fintype.card B := by
  classical
  let target : {a : A // a ∈ matching.support} -> B := fun a =>
    Classical.choose
      ((RelationPartialMatching.mem_support_iff matching a.1).1 a.2)
  have htarget (a : {a : A // a ∈ matching.support}) :
      matching.toFun a.1 = some (target a) :=
    Classical.choose_spec
      ((RelationPartialMatching.mem_support_iff matching a.1).1 a.2)
  have hinjective : Function.Injective target := by
    intro a b hab
    apply Subtype.ext
    exact matching.injective_some (htarget a)
      ((htarget b).trans (congrArg some hab.symm))
  have hcard := Fintype.card_le_of_injective target hinjective
  simpa only [Fintype.card_coe] using hcard



theorem RelationPartialMatching.saturates_all_targets_of_card_support_eq
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    {r : A -> B -> Prop} (matching : RelationPartialMatching r)
    (hcard : matching.support.card = Fintype.card B) (b : B) :
    ∃ a, matching.toFun a = some b := by
  classical
  let Supported := {a : A // a ∈ matching.support}
  let target : Supported -> B := fun a =>
    Classical.choose
      ((RelationPartialMatching.mem_support_iff matching a.1).1 a.2)
  have htarget (a : Supported) :
      matching.toFun a.1 = some (target a) :=
    Classical.choose_spec
      ((RelationPartialMatching.mem_support_iff matching a.1).1 a.2)
  have hinjective : Function.Injective target := by
    intro a c hac
    apply Subtype.ext
    exact matching.injective_some (htarget a)
      ((htarget c).trans (congrArg some hac.symm))
  have hcardTypes : Fintype.card Supported = Fintype.card B := by
    simpa only [Supported, Fintype.card_coe] using hcard
  have hsurjective : Function.Surjective target :=
    ((Fintype.bijective_iff_injective_and_card target).2
      ⟨hinjective, hcardTypes⟩).2
  obtain ⟨a, ha⟩ := hsurjective b
  exact ⟨a.1, (htarget a).trans (congrArg some ha)⟩


noncomputable def RelationPartialMatching.targetPreimage
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r)
    (hsaturated : ∀ b, ∃ a, matching.toFun a = some b) (b : B) : A :=
  Classical.choose (hsaturated b)

theorem RelationPartialMatching.targetPreimage_spec
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r)
    (hsaturated : ∀ b, ∃ a, matching.toFun a = some b) (b : B) :
    matching.toFun (matching.targetPreimage hsaturated b) = some b :=
  Classical.choose_spec (hsaturated b)

theorem RelationPartialMatching.targetPreimage_injective
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r)
    (hsaturated : ∀ b, ∃ a, matching.toFun a = some b) :
    Function.Injective (matching.targetPreimage hsaturated) := by
  intro b c hbc
  apply Option.some.inj
  calc
    some b = matching.toFun (matching.targetPreimage hsaturated b) :=
      (matching.targetPreimage_spec hsaturated b).symm
    _ = matching.toFun (matching.targetPreimage hsaturated c) := congrArg _ hbc
    _ = some c := matching.targetPreimage_spec hsaturated c



structure RelationPartialMatching.HoleState
    {A B : Type*} [Fintype A] (r : A -> B -> Prop) where
  matching : RelationPartialMatching r
  maximum : matching.IsMaximum
  hole : A
  hole_unmatched : hole ∉ matching.support

noncomputable instance instFintypeRelationPartialMatchingHoleState
    {A B : Type*} [Fintype A] [Fintype B] (r : A -> B -> Prop) :
    Fintype (RelationPartialMatching.HoleState r) := by
  classical
  letI : Fintype (RelationPartialMatching r) :=
    instFintypeRelationPartialMatching r
  let encode : RelationPartialMatching.HoleState r ->
      RelationPartialMatching r × A := fun state => (state.matching, state.hole)
  apply Fintype.ofInjective encode
  intro x y h
  cases x
  cases y
  cases h
  rfl



theorem RelationPartialMatching.exists_holeState_of_card_lt
    {A B : Type*} [Fintype A] [Fintype B] (r : A -> B -> Prop)
    (hcard : Fintype.card B < Fintype.card A) :
    Nonempty (RelationPartialMatching.HoleState r) := by
  classical
  obtain ⟨matching, hmaximum⟩ := exists_maximum_relationPartialMatching r
  have hexposed : ∃ a, a ∉ matching.support := by
    by_contra hall
    push Not at hall
    have hsupport : matching.support = Finset.univ :=
      Finset.eq_univ_of_forall hall
    have hle := matching.card_support_le_target
    rw [hsupport, Finset.card_univ] at hle
    omega
  obtain ⟨a, ha⟩ := hexposed
  exact ⟨⟨matching, hmaximum, a, ha⟩⟩


noncomputable def RelationPartialMatching.HoleState.occupant
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) : A :=
  Classical.choose (state.maximum.saturates_target_of_unmatched
    state.hole state.hole_unmatched (natural state.hole) (hnatural state.hole))

theorem RelationPartialMatching.HoleState.occupant_spec
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    state.matching.toFun (state.occupant natural hnatural) =
      some (natural state.hole) :=
  Classical.choose_spec (state.maximum.saturates_target_of_unmatched
    state.hole state.hole_unmatched (natural state.hole) (hnatural state.hole))




noncomputable def RelationPartialMatching.HoleState.move
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    RelationPartialMatching.HoleState r := by
  classical
  let old := state.occupant natural hnatural
  have hold : state.matching.toFun old = some (natural state.hole) := by
    exact state.occupant_spec natural hnatural
  let hne : state.hole ≠ old :=
    state.matching.ne_of_not_mem_support_of_eq_some
      state.hole old (natural state.hole) state.hole_unmatched hold
  let reassigned := state.matching.reassign state.hole old
    (natural state.hole) hne hold (hnatural state.hole)
  have hmaximum : reassigned.IsMaximum := by
    simpa only [reassigned] using state.maximum.reassign
      state.hole old (natural state.hole) state.hole_unmatched hold
        (hnatural state.hole)
  have holdUnmatched : old ∉ reassigned.support := by
    intro hmem
    obtain ⟨b, hb⟩ :=
      (RelationPartialMatching.mem_support_iff reassigned old).1 hmem
    have hnone : reassigned.toFun old = none := by
      simpa only [reassigned] using
        RelationPartialMatching.reassign_apply_old state.matching
          state.hole old (natural state.hole) hne hold (hnatural state.hole)
    rw [hnone] at hb
    contradiction
  exact ⟨reassigned, hmaximum, old, holdUnmatched⟩



noncomputable def RelationPartialMatching.HoleState.occupantAt
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) : A :=
  Classical.choose (state.maximum.saturates_target_of_unmatched
    state.hole state.hole_unmatched b hincident)

theorem RelationPartialMatching.HoleState.occupantAt_spec
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    state.matching.toFun (state.occupantAt b hincident) = some b :=
  Classical.choose_spec (state.maximum.saturates_target_of_unmatched
    state.hole state.hole_unmatched b hincident)




noncomputable def RelationPartialMatching.HoleState.moveAcross
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    RelationPartialMatching.HoleState r := by
  classical
  let old := state.occupantAt b hincident
  have hold : state.matching.toFun old = some b :=
    state.occupantAt_spec b hincident
  let hne : state.hole ≠ old :=
    state.matching.ne_of_not_mem_support_of_eq_some
      state.hole old b state.hole_unmatched hold
  let reassigned := state.matching.reassign state.hole old b hne hold hincident
  have hmaximum : reassigned.IsMaximum := by
    simpa only [reassigned] using state.maximum.reassign
      state.hole old b state.hole_unmatched hold hincident
  have holdUnmatched : old ∉ reassigned.support := by
    intro hmem
    obtain ⟨target, htarget⟩ :=
      (RelationPartialMatching.mem_support_iff reassigned old).1 hmem
    have hnone : reassigned.toFun old = none := by
      simpa only [reassigned] using
        RelationPartialMatching.reassign_apply_old state.matching
          state.hole old b hne hold hincident
    rw [hnone] at htarget
    contradiction
  exact ⟨reassigned, hmaximum, old, holdUnmatched⟩



theorem RelationPartialMatching.HoleState.matching_apply_moveAcross_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    state.matching.toFun (state.moveAcross b hincident).hole = some b := by
  change state.matching.toFun (state.occupantAt b hincident) = some b
  exact state.occupantAt_spec b hincident



theorem RelationPartialMatching.HoleState.moveAcross_matching_apply_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    (state.moveAcross b hincident).matching.toFun state.hole = some b := by
  classical
  unfold RelationPartialMatching.HoleState.moveAcross
  simp only
  apply RelationPartialMatching.reassign_apply_new


theorem RelationPartialMatching.HoleState.hole_ne_moveAcross_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (state : RelationPartialMatching.HoleState r) (b : B)
    (hincident : r state.hole b) :
    state.hole ≠ (state.moveAcross b hincident).hole := by
  intro h
  apply state.hole_unmatched
  apply (RelationPartialMatching.mem_support_iff state.matching state.hole).2
  exact ⟨b, h ▸ state.matching_apply_moveAcross_hole b hincident⟩



theorem RelationPartialMatching.HoleState.matching_apply_move_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    state.matching.toFun (state.move natural hnatural).hole =
      some (natural state.hole) := by
  change state.matching.toFun (state.occupant natural hnatural) =
    some (natural state.hole)
  exact state.occupant_spec natural hnatural


theorem RelationPartialMatching.HoleState.move_matching_apply_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    (state.move natural hnatural).matching.toFun state.hole =
      some (natural state.hole) := by
  classical
  unfold RelationPartialMatching.HoleState.move
  simp only
  apply RelationPartialMatching.reassign_apply_new


theorem RelationPartialMatching.HoleState.hole_ne_move_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    state.hole ≠ (state.move natural hnatural).hole := by
  intro h
  apply state.hole_unmatched
  apply (RelationPartialMatching.mem_support_iff
    state.matching state.hole).2
  exact ⟨natural state.hole,
    h ▸ state.matching_apply_move_hole natural hnatural⟩




theorem RelationPartialMatching.HoleState.move_matching_apply_of_ne
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) (x : A)
    (hxCurrent : x ≠ state.hole)
    (hxNext : x ≠ (state.move natural hnatural).hole) :
    (state.move natural hnatural).matching.toFun x =
      state.matching.toFun x := by
  classical
  unfold RelationPartialMatching.HoleState.move
  simp only
  apply RelationPartialMatching.reassign_apply_of_ne
  · exact hxCurrent
  · exact hxNext


noncomputable def RelationPartialMatching.HoleState.naturalSupport
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (state : RelationPartialMatching.HoleState r) :
    Finset A := by
  classical
  exact Finset.univ.filter fun a =>
    state.matching.toFun a = some (natural a)



theorem RelationPartialMatching.HoleState.card_naturalSupport_lt_move_of_ne
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (hne : natural state.hole ≠
      natural (state.move natural hnatural).hole) :
    (state.naturalSupport natural).card <
      ((state.move natural hnatural).naturalSupport natural).card := by
  classical
  let moved := state.move natural hnatural
  have hcurrentNot : state.hole ∉ state.naturalSupport natural := by
    intro hmem
    have hmatch : state.matching.toFun state.hole =
        some (natural state.hole) := by
      simpa only [RelationPartialMatching.HoleState.naturalSupport,
        Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    exact state.hole_unmatched
      ((RelationPartialMatching.mem_support_iff state.matching state.hole).2
        ⟨natural state.hole, hmatch⟩)
  have hcurrentMem : state.hole ∈ moved.naturalSupport natural := by
    simp only [RelationPartialMatching.HoleState.naturalSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact state.move_matching_apply_hole natural hnatural
  have hsubset : state.naturalSupport natural ⊆
      moved.naturalSupport natural := by
    intro x hx
    have hxMatch : state.matching.toFun x = some (natural x) := by
      simpa only [RelationPartialMatching.HoleState.naturalSupport,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hxCurrent : x ≠ state.hole := by
      intro h
      exact hcurrentNot (h ▸ hx)
    have hxNext : x ≠ moved.hole := by
      intro h
      have hoccupied := state.matching_apply_move_hole natural hnatural
      rw [← h] at hoccupied
      have htargets : natural x = natural state.hole := by
        exact Option.some.inj (hxMatch.symm.trans hoccupied)
      exact hne (htargets.symm.trans (congrArg natural h))
    simp only [RelationPartialMatching.HoleState.naturalSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact (state.move_matching_apply_of_ne natural hnatural x
      hxCurrent hxNext).trans hxMatch
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_subset_ne).2
  refine ⟨hsubset, ?_⟩
  intro heq
  exact hcurrentNot (heq ▸ hcurrentMem)




theorem RelationPartialMatching.exists_maximalNatural_holeState_collision
    {A B : Type*} [Fintype A] [Fintype B] (r : A -> B -> Prop)
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (hcard : Fintype.card B < Fintype.card A) :
    ∃ state : RelationPartialMatching.HoleState r,
      state.hole ≠ (state.move natural hnatural).hole ∧
        natural state.hole = natural (state.move natural hnatural).hole := by
  classical
  letI : Fintype (RelationPartialMatching.HoleState r) :=
    instFintypeRelationPartialMatchingHoleState r
  obtain ⟨initial⟩ := RelationPartialMatching.exists_holeState_of_card_lt
    r hcard
  obtain ⟨state, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (RelationPartialMatching.HoleState r))
    (fun s => (s.naturalSupport natural).card) ⟨initial, Finset.mem_univ _⟩
  refine ⟨state, state.hole_ne_move_hole natural hnatural, ?_⟩
  by_contra hne
  have hlt := state.card_naturalSupport_lt_move_of_ne
    natural hnatural hne
  have hle := hmax (state.move natural hnatural) (Finset.mem_univ _)
  omega




theorem RelationPartialMatching.HoleState.move_move_hole_eq_of_natural_eq
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (heq : natural state.hole =
      natural (state.move natural hnatural).hole) :
    ((state.move natural hnatural).move natural hnatural).hole =
      state.hole := by
  let moved := state.move natural hnatural
  apply moved.matching.injective_some
    (moved.matching_apply_move_hole natural hnatural)
  exact (state.move_matching_apply_hole natural hnatural).trans
    (congrArg some heq)



theorem RelationPartialMatching.HoleState.iterate_matching_apply_next_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) (n : Nat) :
    let move := RelationPartialMatching.HoleState.move natural hnatural
    (move^[n] state).matching.toFun (move^[n + 1] state).hole =
      some (natural (move^[n] state).hole) := by
  dsimp only
  let move := RelationPartialMatching.HoleState.move natural hnatural
  have hsucc : move^[n + 1] state = move (move^[n] state) := by
    rw [show n + 1 = Nat.succ n by omega]
    exact Function.iterate_succ_apply' move n state
  rw [hsucc]
  exact (move^[n] state).matching_apply_move_hole natural hnatural



theorem RelationPartialMatching.HoleState.iterate_succ_matching_apply_hole
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) (n : Nat) :
    let move := RelationPartialMatching.HoleState.move natural hnatural
    (move^[n + 1] state).matching.toFun (move^[n] state).hole =
      some (natural (move^[n] state).hole) := by
  dsimp only
  let move := RelationPartialMatching.HoleState.move natural hnatural
  have hsucc : move^[n + 1] state = move (move^[n] state) := by
    rw [show n + 1 = Nat.succ n by omega]
    exact Function.iterate_succ_apply' move n state
  rw [hsucc]
  exact (move^[n] state).move_matching_apply_hole natural hnatural



theorem RelationPartialMatching.HoleState.iterate_matching_apply_eq_of_avoids
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (start stop : Nat) (hstartStop : start ≤ stop) (x : A)
    (havoids : ∀ n : Nat, start ≤ n -> n < stop ->
      x ≠ ((RelationPartialMatching.HoleState.move
          natural hnatural)^[n] state).hole ∧
        x ≠ ((RelationPartialMatching.HoleState.move
          natural hnatural)^[n + 1] state).hole) :
    ((RelationPartialMatching.HoleState.move
        natural hnatural)^[stop] state).matching.toFun x =
      ((RelationPartialMatching.HoleState.move
        natural hnatural)^[start] state).matching.toFun x := by
  let move := RelationPartialMatching.HoleState.move natural hnatural
  change (move^[stop] state).matching.toFun x =
    (move^[start] state).matching.toFun x
  induction stop, hstartStop using Nat.le_induction with
  | base => rfl
  | succ stop hstartLe hprevious =>
      have hstep : move^[stop + 1] state = move (move^[stop] state) := by
        rw [show stop + 1 = Nat.succ stop by omega]
        exact Function.iterate_succ_apply' move stop state
      have havoid := havoids stop hstartLe (by omega)
      have hxNext : x ≠ (move (move^[stop] state)).hole := by
        rw [← hstep]
        exact havoid.2
      calc
        (move^[stop + 1] state).matching.toFun x =
            (move^[stop] state).matching.toFun x := by
          rw [hstep]
          exact (move^[stop] state).move_matching_apply_of_ne
            natural hnatural x havoid.1 hxNext
        _ = (move^[start] state).matching.toFun x := by
          apply hprevious
          intro n hnStart hnStop
          exact havoids n hnStart (hnStop.trans_le (Nat.le_succ stop))




theorem RelationPartialMatching.HoleState.first_repeat_interior_matching
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((RelationPartialMatching.HoleState.move
          natural hnatural)^[start] state).hole =
        ((RelationPartialMatching.HoleState.move
          natural hnatural)^[stop] state).hole)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((RelationPartialMatching.HoleState.move
          natural hnatural)^[a] state).hole ≠
        ((RelationPartialMatching.HoleState.move
          natural hnatural)^[b] state).hole)
    (q : Nat) (hqStart : start < q) (hqStop : q < stop) :
    ((RelationPartialMatching.HoleState.move
        natural hnatural)^[stop] state).matching.toFun
          (((RelationPartialMatching.HoleState.move
            natural hnatural)^[q] state).hole) =
      some (natural
        (((RelationPartialMatching.HoleState.move
          natural hnatural)^[q] state).hole)) := by
  let move := RelationPartialMatching.HoleState.move natural hnatural
  change (move^[stop] state).matching.toFun (move^[q] state).hole =
    some (natural (move^[q] state).hole)
  have hassigned :=
    RelationPartialMatching.HoleState.iterate_succ_matching_apply_hole
      natural hnatural state q
  change (move^[q + 1] state).matching.toFun (move^[q] state).hole =
    some (natural (move^[q] state).hole) at hassigned
  have hretained :=
    RelationPartialMatching.HoleState.iterate_matching_apply_eq_of_avoids
      natural hnatural state (q + 1) stop (by omega)
        (move^[q] state).hole
  rw [hretained]
  · exact hassigned
  · intro n hnStart hnStop
    constructor
    · exact hdistinct q n (by omega) hnStop
    · by_cases hn : n + 1 < stop
      · exact hdistinct q (n + 1) (by omega) hn
      · have hnEq : n + 1 = stop := by omega
        rw [hnEq, ← hrepeat]
        exact (hdistinct start q hqStart hqStop).symm




theorem RelationPartialMatching.HoleState.first_repeat_interior_natural_ne
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((RelationPartialMatching.HoleState.move
          natural hnatural)^[start] state).hole =
        ((RelationPartialMatching.HoleState.move
          natural hnatural)^[stop] state).hole)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((RelationPartialMatching.HoleState.move
          natural hnatural)^[a] state).hole ≠
        ((RelationPartialMatching.HoleState.move
          natural hnatural)^[b] state).hole)
    (q u : Nat) (hqStart : start < q) (hqStop : q < stop)
    (huStart : start < u) (huStop : u < stop) (hqu : q ≠ u) :
    natural (((RelationPartialMatching.HoleState.move
        natural hnatural)^[q] state).hole) ≠
      natural (((RelationPartialMatching.HoleState.move
        natural hnatural)^[u] state).hole) := by
  let move := RelationPartialMatching.HoleState.move natural hnatural
  change natural (move^[q] state).hole ≠ natural (move^[u] state).hole
  intro hnaturalEq
  have hqMatch :=
    RelationPartialMatching.HoleState.first_repeat_interior_matching
      natural hnatural state start stop hstartStop hrepeat hdistinct
        q hqStart hqStop
  have huMatch :=
    RelationPartialMatching.HoleState.first_repeat_interior_matching
      natural hnatural state start stop hstartStop hrepeat hdistinct
        u huStart huStop
  have hholes : (move^[q] state).hole = (move^[u] state).hole :=
    (move^[stop] state).matching.injective_some hqMatch
      (huMatch.trans (congrArg some hnaturalEq.symm))
  rcases lt_or_gt_of_ne hqu with hqu' | huq'
  · exact (hdistinct q u hqu' huStop) hholes
  · exact (hdistinct u q huq' hqStop) hholes.symm



theorem RelationPartialMatching.HoleState.exists_minimal_hole_repeat
    {A B : Type*} [Fintype A] {r : A -> B -> Prop}
    (natural : A -> B) (hnatural : ∀ a, r a (natural a))
    (state : RelationPartialMatching.HoleState r) :
    let move := RelationPartialMatching.HoleState.move natural hnatural
    ∃ start stop : Nat, start < stop ∧ stop ≤ Fintype.card A ∧
      (move^[start] state).hole = (move^[stop] state).hole ∧
      ∀ a b : Nat, a < b -> b < stop ->
        (move^[a] state).hole ≠ (move^[b] state).hole := by
  classical
  dsimp only
  let move := RelationPartialMatching.HoleState.move natural hnatural
  let exposed : Fin (Fintype.card A + 1) -> A := fun n =>
    (move^[n.1] state).hole
  have hnotinj : ¬Function.Injective exposed := by
    intro hinj
    have hcard := Fintype.card_le_of_injective exposed hinj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨u, v, heq, huv⟩ := Function.not_injective_iff.mp hnotinj
  obtain ⟨i0, j0, hij0, heq0, hj0Bound⟩ :
      ∃ i0 j0 : Nat, i0 < j0 ∧
        (move^[i0] state).hole = (move^[j0] state).hole ∧
        j0 ≤ Fintype.card A := by
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · exact ⟨u.1, v.1, huv', heq, Nat.le_of_lt_succ v.2⟩
    · exact ⟨v.1, u.1, hvu', heq.symm, Nat.le_of_lt_succ u.2⟩
  let P := fun n : Nat => ∃ i < n,
    (move^[i] state).hole = (move^[n] state).hole
  have hP : ∃ n, P n := ⟨j0, i0, hij0, heq0⟩
  let stop := Nat.find hP
  obtain ⟨start, hstartStop, hrepeat⟩ := Nat.find_spec hP
  have hstopBound : stop ≤ Fintype.card A := by
    exact (Nat.find_min' hP ⟨i0, hij0, heq0⟩).trans hj0Bound
  refine ⟨start, stop, hstartStop, hstopBound, hrepeat, ?_⟩
  intro a b hab hbStop habHole
  have hPb : P b := ⟨a, hab, habHole⟩
  have hstopLe := Nat.find_min' hP hPb
  exact (Nat.not_le_of_lt hbStop) hstopLe



theorem card_subtype_le_of_tag_preserving_fiberwise_discrepancy
    {A S : Type*} [Fintype A] (P Q : A -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (sourceTag : {a : A // P a ∧ ¬ Q a} -> S)
    (targetTag : {a : A // ¬ P a ∧ Q a} -> S)
    (f : {a : A // P a ∧ ¬ Q a} -> {a : A // ¬ P a ∧ Q a})
    (htag : ∀ x, targetTag (f x) = sourceTag x)
    (hfiber : ∀ s, Function.Injective fun
      x : {x : {a : A // P a ∧ ¬ Q a} // sourceTag x = s} => f x.1) :
    Fintype.card {a : A // P a} <= Fintype.card {a : A // Q a} := by
  exact card_subtype_le_of_discrepancyEmbedding P Q
    (embeddingOf_tag_preserving_fiberwise sourceTag targetTag f htag hfiber)



noncomputable def finiteRelationNeighborhood
    {A : Type*} [Fintype A] (R : A -> A -> Prop) (S : Finset A) :
    Finset A := by
  classical
  exact Finset.univ.filter fun y => ∃ x ∈ S, R x y


noncomputable def finiteCommonClosureStep
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) : Finset A := by
  classical
  exact S ∪ (finiteRelationNeighborhood R S).filter fun y => P y ∧ Q y

@[simp] theorem mem_finiteCommonClosureStep
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (x : A) :
    x ∈ finiteCommonClosureStep P Q R S ↔
      x ∈ S ∨
        (x ∈ finiteRelationNeighborhood R S ∧ P x ∧ Q x) := by
  classical
  simp [finiteCommonClosureStep]

theorem subset_finiteCommonClosureStep
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) :
    S ⊆ finiteCommonClosureStep P Q R S := by
  classical
  exact Finset.subset_union_left

theorem finiteRelationNeighborhood_mono
    {A : Type*} [Fintype A] (R : A -> A -> Prop)
    {S T : Finset A} (hST : S ⊆ T) :
    finiteRelationNeighborhood R S ⊆ finiteRelationNeighborhood R T := by
  classical
  intro y hy
  obtain ⟨x, hx, hxy⟩ := Finset.mem_filter.mp hy |>.2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, x, hST hx, hxy⟩

theorem finiteCommonClosureStep_mono
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    {S T : Finset A} (hST : S ⊆ T) :
    finiteCommonClosureStep P Q R S ⊆
      finiteCommonClosureStep P Q R T := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hxS | hxCommon
  · exact Finset.mem_union_left _ (hST hxS)
  · apply Finset.mem_union_right
    have hx' := Finset.mem_filter.mp hxCommon
    exact Finset.mem_filter.mpr ⟨
      finiteRelationNeighborhood_mono R hST hx'.1, hx'.2⟩


noncomputable def finiteCommonClosureIter
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) : Nat -> Finset A
  | 0 => S
  | n + 1 => finiteCommonClosureStep P Q R
      (finiteCommonClosureIter P Q R S n)

theorem finiteCommonClosureIter_subset_succ
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (n : Nat) :
    finiteCommonClosureIter P Q R S n ⊆
      finiteCommonClosureIter P Q R S (n + 1) := by
  rw [finiteCommonClosureIter]
  exact subset_finiteCommonClosureStep P Q R _

theorem finiteCommonClosureIter_zero_subset
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (n : Nat) :
    S ⊆ finiteCommonClosureIter P Q R S n := by
  induction n with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
      exact ih.trans (finiteCommonClosureIter_subset_succ P Q R S n)

theorem finiteCommonClosureIter_preserves_left
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (hS : ∀ x ∈ S, P x) :
    ∀ n x, x ∈ finiteCommonClosureIter P Q R S n -> P x := by
  intro n
  induction n with
  | zero => exact fun x hx => hS x hx
  | succ n ih =>
      intro x hx
      rw [finiteCommonClosureIter] at hx
      rcases (mem_finiteCommonClosureStep P Q R _ x).mp hx with hx | hx
      · exact ih x hx
      · exact hx.2.1




theorem finiteCommonClosureIter_common_mem_neighborhood
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (hS : ∀ x ∈ S, ¬ Q x) :
    ∀ n x, x ∈ finiteCommonClosureIter P Q R S n -> Q x ->
      x ∈ finiteRelationNeighborhood R
        (finiteCommonClosureIter P Q R S n) := by
  classical
  intro n
  induction n with
  | zero =>
      intro x hx hxQ
      exact False.elim (hS x hx hxQ)
  | succ n ih =>
      intro x hx hxQ
      rw [finiteCommonClosureIter] at hx ⊢
      rcases (mem_finiteCommonClosureStep P Q R _ x).mp hx with
        hxOld | hxNew
      · exact finiteRelationNeighborhood_mono R
          (finiteCommonClosureIter_subset_succ P Q R S n)
          (ih x hxOld hxQ)
      · exact finiteRelationNeighborhood_mono R
          (finiteCommonClosureIter_subset_succ P Q R S n) hxNew.1

theorem finiteCommonClosureIter_succ_start
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) (n : Nat) :
    finiteCommonClosureIter P Q R S (n + 1) =
      finiteCommonClosureIter P Q R
        (finiteCommonClosureStep P Q R S) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change finiteCommonClosureStep P Q R
          (finiteCommonClosureIter P Q R S (n + 1)) =
        finiteCommonClosureStep P Q R
          (finiteCommonClosureIter P Q R
            (finiteCommonClosureStep P Q R S) n)
      rw [ih]



theorem exists_finiteCommonClosureIter_fixed
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    (S : Finset A) :
    ∃ n ≤ Fintype.card A - S.card,
      finiteCommonClosureIter P Q R S (n + 1) =
        finiteCommonClosureIter P Q R S n := by
  classical
  by_cases hfixed : finiteCommonClosureStep P Q R S = S
  · exact ⟨0, Nat.zero_le _, hfixed⟩
  · let S' := finiteCommonClosureStep P Q R S
    have hsubset : S ⊂ S' :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨subset_finiteCommonClosureStep P Q R S,
          fun h => hfixed h.symm⟩
    have hcard : S.card < S'.card := Finset.card_lt_card hsubset
    have hS'le : S'.card ≤ Fintype.card A := by
      simpa only [Finset.card_univ] using Finset.card_le_univ S'
    have hremaining : Fintype.card A - S'.card <
        Fintype.card A - S.card := by
      omega
    obtain ⟨n, hn, hstep⟩ :=
      exists_finiteCommonClosureIter_fixed P Q R S'
    refine ⟨n + 1, ?_, ?_⟩
    · omega
    · calc
        finiteCommonClosureIter P Q R S (n + 1 + 1) =
            finiteCommonClosureIter P Q R S' (n + 1) := by
          simpa only [S'] using
            finiteCommonClosureIter_succ_start P Q R S (n + 1)
        _ = finiteCommonClosureIter P Q R S' n := hstep
        _ = finiteCommonClosureIter P Q R S (n + 1) := by
          simpa only [S'] using
            (finiteCommonClosureIter_succ_start P Q R S n).symm
termination_by Fintype.card A - S.card
decreasing_by exact hremaining





theorem card_leftOnly_le_rightOnly_of_commonClosed_expansion
    {A : Type*} [Fintype A] (P Q : A -> Prop) (R : A -> A -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (T : Finset A)
    (hrel : ∀ {x y}, R x y -> P x ∧ Q y)
    (hnegative : Finset.univ.filter (fun x => P x ∧ ¬ Q x) ⊆ T)
    (hleft : ∀ x ∈ T, P x)
    (hclosed : finiteCommonClosureStep P Q R T = T)
    (hexpand : T.card ≤ (finiteRelationNeighborhood R T).card) :
    (Finset.univ.filter fun x => P x ∧ ¬ Q x).card ≤
      (Finset.univ.filter fun x => ¬ P x ∧ Q x).card := by
  classical
  let N := Finset.univ.filter fun x => P x ∧ ¬ Q x
  let Pos := Finset.univ.filter fun x => ¬ P x ∧ Q x
  let TC := T.filter Q
  let U := finiteRelationNeighborhood R T
  let UC := U.filter P
  let UP := U.filter fun x => ¬ P x
  have hTdecomp : T = N ∪ TC := by
    ext x
    constructor
    · intro hx
      by_cases hxQ : Q x
      · exact Finset.mem_union_right N (Finset.mem_filter.mpr ⟨hx, hxQ⟩)
      · exact Finset.mem_union_left TC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hleft x hx, hxQ⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxN | hxTC
      · exact hnegative hxN
      · exact (Finset.mem_filter.mp hxTC).1
  have hN_TC : Disjoint N TC := by
    rw [Finset.disjoint_left]
    intro x hxN hxTC
    exact (Finset.mem_filter.mp hxN).2.2 (Finset.mem_filter.mp hxTC).2
  have hTcard : T.card = N.card + TC.card := by
    rw [hTdecomp, Finset.card_union_of_disjoint hN_TC]
  have hUQ : ∀ x ∈ U, Q x := by
    intro y hy
    obtain ⟨x, -, hxy⟩ := Finset.mem_filter.mp hy |>.2
    exact (hrel hxy).2
  have hUdecomp : U = UP ∪ UC := by
    ext x
    constructor
    · intro hx
      by_cases hxP : P x
      · exact Finset.mem_union_right UP (Finset.mem_filter.mpr ⟨hx, hxP⟩)
      · exact Finset.mem_union_left UC (Finset.mem_filter.mpr ⟨hx, hxP⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxUP | hxUC
      · exact (Finset.mem_filter.mp hxUP).1
      · exact (Finset.mem_filter.mp hxUC).1
  have hUP_UC : Disjoint UP UC := by
    rw [Finset.disjoint_left]
    intro x hxUP hxUC
    exact (Finset.mem_filter.mp hxUP).2 (Finset.mem_filter.mp hxUC).2
  have hUcard : U.card = UP.card + UC.card := by
    rw [hUdecomp, Finset.card_union_of_disjoint hUP_UC]
  have hUC_TC : UC ⊆ TC := by
    intro x hx
    have hxU := (Finset.mem_filter.mp hx).1
    have hxP := (Finset.mem_filter.mp hx).2
    have hxQ := hUQ x hxU
    have hxStep : x ∈ finiteCommonClosureStep P Q R T := by
      exact (mem_finiteCommonClosureStep P Q R T x).mpr
        (Or.inr ⟨hxU, hxP, hxQ⟩)
    exact Finset.mem_filter.mpr ⟨hclosed ▸ hxStep, hxQ⟩
  have hUP_Pos : UP ⊆ Pos := by
    intro x hx
    have hxU := (Finset.mem_filter.mp hx).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      (Finset.mem_filter.mp hx).2, hUQ x hxU⟩
  have hUCcard := Finset.card_le_card hUC_TC
  have hUPcard := Finset.card_le_card hUP_Pos
  rw [hTcard, hUcard] at hexpand
  change N.card ≤ Pos.card
  omega

end StatMech.FrontierA
