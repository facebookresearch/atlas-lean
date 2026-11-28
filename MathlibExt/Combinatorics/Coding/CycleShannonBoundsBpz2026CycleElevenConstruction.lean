/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`ShannonBounds/BaseC11Data.lean` (shannon-capacity-lean, revision
`aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65`): the two base lists and the three port pairs.
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/

module

public import MathlibExt.Combinatorics.Coding.CycleShannonBoundsBpz2026CycleTwentyOneConstruction
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# An independent code in the 174th strong power of the eleven-cycle

The dimension-three starting tuple has profile `(148, 3, 148, 142)`. Iterating the
valid-tuple product along the eleven-cycle schedule yields a code with exactly the code
coordinate of the resulting fifty-eight-block profile.

The product uses tuples whose distinct ports have separated endpoints, even across labels.
Auxiliary vertices are marked neutral or assigned one label; any confusable port endpoint
must have that label, and every assigned label has a witnessing endpoint. Thus the
neutral part consists exactly of the vertices that are confusable with no endpoint.

## References

* Pjotr Buys, Sven Polak, and Jeroen Zuiddam, *Lean-verified lower bounds for the Shannon
  capacity of odd cycles*, arXiv:2607.29681v1 (2026), §2, Theorem 1 and Example 1, and §3,
  "The cycle C11". See also the authors' accompanying data, `ShannonBounds/BaseC11Data.lean`
  in https://github.com/spectra-research/shannon-capacity-lean at
  `aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65`.
* Yu Gao, *A Recursive Construction Improving the Lower Bound on the Shannon Capacity of $C_7$*,
  arXiv:2607.27869 (2026), Definitions 2–3 and Lemma 4.
* L. D. Baumert, R. J. McEliece, Eugene Rodemich, Howard C. Rumsey, Jr., Richard Stanley,
  and Herbert Taylor, *A combinatorial packing problem*, in *Computers in Algebra and Number
  Theory*, SIAM-AMS Proceedings IV (1971), pp. 97–108, for the 148-word cube construction.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- Indexed form of the tuple used in the construction. `B` is the code with the port
parents removed, `P` indexes ports, and `N` and `A` index the two parts of the auxiliary set.
Distinct ports cannot conflict, regardless of the endpoint labels. -/
private structure PortTuple {V : Type} (rel : V → V → Prop) where
  B : Type
  P : Type
  N : Type
  A : Type
  finiteB : Fintype B
  finiteP : Fintype P
  finiteN : Fintype N
  finiteA : Fintype A
  core : B → V
  endpoint : Bool → P → V
  side : P → Bool
  aux : N ⊕ A → V
  label : A → Bool
  core_sep : ∀ {i j}, rel (core i) (core j) → i = j
  core_port : ∀ i p c, ¬ rel (core i) (endpoint c p)
  ports_sep : ∀ {p q b c}, rel (endpoint b p) (endpoint c q) → p = q
  ends_ne : ∀ p, endpoint false p ≠ endpoint true p
  ends_rel : ∀ p, rel (endpoint false p) (endpoint true p)
  aux_sep : ∀ {x y}, rel (aux x) (aux y) → x = y
  aux_label : ∀ {x p c}, rel (aux x) (endpoint c p) →
    x.elim (fun _ => none) (some ∘ label) = some c
  label_hit : ∀ a, ∃ p, rel (aux (.inr a)) (endpoint (label a) p)

namespace PortTuple

attribute [local instance] finiteB finiteP finiteN finiteA

variable {V W Z : Type} {r : V → V → Prop} {s : W → W → Prop} {t : Z → Z → Prop}

private def profile (T : PortTuple r) : BPZProfile :=
  ⟨Fintype.card T.B + Fintype.card T.P, Fintype.card T.P,
   Fintype.card T.N + Fintype.card T.A, Fintype.card T.N⟩

private def word (T : PortTuple r) : T.B ⊕ T.P → V :=
  Sum.elim T.core (fun p => T.endpoint (T.side p) p)

private theorem word_sep (T : PortTuple r) (hr : Std.Symm r) {i j : T.B ⊕ T.P}
    (h : r (T.word i) (T.word j)) : i = j := by
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (T.core_sep h)
  · exact (T.core_port _ _ _ h).elim
  · exact (T.core_port _ _ _ (hr.symm _ _ h)).elim
  · exact congrArg Sum.inr (T.ports_sep h)

private def map (T : PortTuple r) (e : V ↪ Z) (he : ∀ x y, t (e x) (e y) ↔ r x y) :
    PortTuple t where
  B := T.B
  P := T.P
  N := T.N
  A := T.A
  finiteB := T.finiteB
  finiteP := T.finiteP
  finiteN := T.finiteN
  finiteA := T.finiteA
  core := e ∘ T.core
  endpoint c := e ∘ T.endpoint c
  side := T.side
  aux := e ∘ T.aux
  label := T.label
  core_sep h := T.core_sep ((he _ _).mp h)
  core_port i p c h := T.core_port i p c ((he _ _).mp h)
  ports_sep h := T.ports_sep ((he _ _).mp h)
  ends_ne p h := T.ends_ne p (e.injective h)
  ends_rel p := (he _ _).mpr (T.ends_rel p)
  aux_sep h := T.aux_sep ((he _ _).mp h)
  aux_label h := T.aux_label ((he _ _).mp h)
  label_hit a := by
    obtain ⟨p, hp⟩ := T.label_hit a
    exact ⟨p, (he _ _).mpr hp⟩

private theorem profile_map (T : PortTuple r) (e : V ↪ Z)
    (he : ∀ x y, t (e x) (e y) ↔ r x y) : (T.map e he).profile = T.profile := rfl

section Product

private def foot (T : PortTuple r) (x : T.N ⊕ T.A) : Option Bool :=
  x.elim (fun _ => none) (some ∘ T.label)

private abbrev Slot (T : PortTuple r) (U : PortTuple s) :=
  (T.B × U.B) ⊕ ((T.N ⊕ T.A) × U.P) ⊕ (T.P × (U.N ⊕ U.A))

-- A slot identifies a code word, or both endpoints of a new port. A neutral auxiliary
-- vertex leaves the endpoint label free. A nonneutral vertex forces the label.
private def slotWord (T : PortTuple r) (U : PortTuple s) (c : Bool) : Slot T U → V × W
  | .inl (i, j) => (T.core i, U.core j)
  | .inr (.inl (x, p)) => (T.aux x, U.endpoint ((T.foot x).getD c) p)
  | .inr (.inr (p, y)) => (T.endpoint (((U.foot y).map not).getD c) p, U.aux y)

private def pairRel (r : V → V → Prop) (s : W → W → Prop) (x y : V × W) : Prop :=
  r x.1 y.1 ∧ s x.2 y.2

private theorem horizontal_vertical (T : PortTuple r) (U : PortTuple s) (hs : Std.Symm s)
    {x : T.N ⊕ T.A} {y : U.N ⊕ U.A} {p : T.P} {q : U.P} {b c : Bool}
    (h : pairRel r s (T.slotWord U b (.inr (.inl (x, q))))
      (T.slotWord U c (.inr (.inr (p, y))))) : False := by
  let d := (T.foot x).getD b
  let e := ((U.foot y).map not).getD c
  have hx : T.foot x = some e := T.aux_label h.1
  have hy : U.foot y = some d := U.aux_label (hs.symm _ _ h.2)
  have hd : d = e := by simp [d, hx]
  have he : e = !d := by simp [e, hy]
  exact (by decide : ∀ a : Bool, a ≠ !a) d (hd.trans he)

private theorem slot_sep (T : PortTuple r) (U : PortTuple s)
    (hr : Std.Symm r) (hs : Std.Symm s) {b c : Bool}
    {i j : Slot T U} (h : pairRel r s (T.slotWord U b i) (T.slotWord U c j)) : i = j := by
  rcases i with ⟨a, b⟩ | ⟨x, p⟩ | ⟨p, y⟩ <;>
    rcases j with ⟨a', b'⟩ | ⟨x', p'⟩ | ⟨p', y'⟩
  · exact congrArg Sum.inl (Prod.ext (T.core_sep h.1) (U.core_sep h.2))
  · exact (U.core_port _ _ _ h.2).elim
  · exact (T.core_port _ _ _ h.1).elim
  · exact (U.core_port _ _ _ (hs.symm _ _ h.2)).elim
  · exact congrArg (Sum.inr ∘ Sum.inl) (Prod.ext (T.aux_sep h.1) (U.ports_sep h.2))
  · exact (T.horizontal_vertical U hs h).elim
  · exact (T.core_port _ _ _ (hr.symm _ _ h.1)).elim
  · exact (T.horizontal_vertical U hs ⟨hr.symm _ _ h.1, hs.symm _ _ h.2⟩).elim
  · exact congrArg (Sum.inr ∘ Sum.inr) (Prod.ext (T.ports_sep h.1) (U.aux_sep h.2))

private abbrev ProductB (T : PortTuple r) (U : PortTuple s) :=
  (T.B × U.B) ⊕ (T.A × U.P) ⊕ (T.P × U.A)
private abbrev ProductP (T : PortTuple r) (U : PortTuple s) := (T.N × U.P) ⊕ (T.P × U.N)
private abbrev ProductN (T : PortTuple r) (U : PortTuple s) := (T.N × U.N) ⊕ (T.A × U.A)
private abbrev ProductA (T : PortTuple r) (U : PortTuple s) := (T.N × U.A) ⊕ (T.A × U.N)

private def coreSlot (T : PortTuple r) (U : PortTuple s) : ProductB T U → Slot T U
  | .inl ij => .inl ij
  | .inr (.inl (x, p)) => .inr (.inl (.inr x, p))
  | .inr (.inr (p, y)) => .inr (.inr (p, .inr y))

private def portSlot (T : PortTuple r) (U : PortTuple s) : ProductP T U → Slot T U
  | .inl (x, p) => .inr (.inl (.inl x, p))
  | .inr (p, y) => .inr (.inr (p, .inl y))

private theorem coreSlot_injective (T : PortTuple r) (U : PortTuple s)
    : Function.Injective (coreSlot T U) := by
  rintro (⟨i, j⟩ | ⟨x, p⟩ | ⟨p, y⟩) (⟨i', j'⟩ | ⟨x', p'⟩ | ⟨p', y'⟩) <;>
    simp [coreSlot]

private theorem portSlot_injective (T : PortTuple r) (U : PortTuple s)
    : Function.Injective (portSlot T U) := by
  rintro (⟨x, p⟩ | ⟨p, y⟩) (⟨x', p'⟩ | ⟨p', y'⟩) <;> simp [portSlot]

private theorem coreSlot_ne_portSlot (T : PortTuple r) (U : PortTuple s)
    (i : ProductB T U) (p : ProductP T U) :
    T.coreSlot U i ≠ T.portSlot U p := by
  rcases i with ij | ⟨x, a⟩ | ⟨a, y⟩ <;> rcases p with ⟨x', a'⟩ | ⟨a', y'⟩ <;>
    simp [coreSlot, portSlot]

private def auxSlot (T : PortTuple r) (U : PortTuple s) :
    ProductN T U ⊕ ProductA T U → (T.N ⊕ T.A) × (U.N ⊕ U.A)
  | .inl (.inl (x, y)) => (.inl x, .inl y)
  | .inl (.inr (x, y)) => (.inr x, .inr y)
  | .inr (.inl (x, y)) => (.inl x, .inr y)
  | .inr (.inr (x, y)) => (.inr x, .inl y)

private theorem auxSlot_injective (T : PortTuple r) (U : PortTuple s)
    : Function.Injective (auxSlot T U) := by
  rintro ((⟨x, y⟩ | ⟨x, y⟩) | (⟨x, y⟩ | ⟨x, y⟩))
    ((⟨x', y'⟩ | ⟨x', y'⟩) | (⟨x', y'⟩ | ⟨x', y'⟩)) <;> simp [auxSlot]

private def productLabel (T : PortTuple r) (U : PortTuple s) : ProductA T U → Bool
  | .inl (_, y) => U.label y
  | .inr (x, _) => T.label x

private theorem product_aux_label (T : PortTuple r) (U : PortTuple s)
    {a : ProductN T U ⊕ ProductA T U} {p : ProductP T U}
    {c : Bool} (h : pairRel r s (T.aux (T.auxSlot U a).1, U.aux (T.auxSlot U a).2)
      (T.slotWord U c (T.portSlot U p))) :
    a.elim (fun _ => none) (some ∘ T.productLabel U) = some c := by
  rcases p with ⟨x, p⟩ | ⟨p, y⟩
  · have hx : (T.auxSlot U a).1 = .inl x := T.aux_sep h.1
    have hy : U.foot (T.auxSlot U a).2 = some c := U.aux_label h.2
    rcases a with (⟨x', y'⟩ | ⟨x', y'⟩) | (⟨x', y'⟩ | ⟨x', y'⟩) <;>
      simp_all [auxSlot, foot, productLabel]
  · have hx : T.foot (T.auxSlot U a).1 = some c := T.aux_label h.1
    have hy : (T.auxSlot U a).2 = .inl y := U.aux_sep h.2
    rcases a with (⟨x', y'⟩ | ⟨x', y'⟩) | (⟨x', y'⟩ | ⟨x', y'⟩) <;>
      simp_all [auxSlot, foot, productLabel]

private def product (T : PortTuple r) (U : PortTuple s)
    (hr : Std.Refl r) (hs : Std.Refl s)
    (hr' : Std.Symm r) (hs' : Std.Symm s) : PortTuple (pairRel r s) where
  B := ProductB T U
  P := ProductP T U
  N := ProductN T U
  A := ProductA T U
  finiteB := inferInstance
  finiteP := inferInstance
  finiteN := inferInstance
  finiteA := inferInstance
  core := T.slotWord U false ∘ T.coreSlot U
  endpoint c := T.slotWord U c ∘ T.portSlot U
  side := Sum.elim (fun p => U.side p.2) (fun p => T.side p.1)
  aux a := (T.aux (T.auxSlot U a).1, U.aux (T.auxSlot U a).2)
  label := T.productLabel U
  core_sep h := T.coreSlot_injective U (T.slot_sep U hr' hs' h)
  core_port i p _ h := T.coreSlot_ne_portSlot U i p (T.slot_sep U hr' hs' h)
  ports_sep h := T.portSlot_injective U (T.slot_sep U hr' hs' h)
  ends_ne := by
    rintro (⟨x, p⟩ | ⟨p, y⟩) h
    · exact U.ends_ne p (congrArg Prod.snd h)
    · exact T.ends_ne p (congrArg Prod.fst h)
  ends_rel := by
    rintro (⟨x, p⟩ | ⟨p, y⟩)
    · exact ⟨hr.refl _, U.ends_rel p⟩
    · exact ⟨T.ends_rel p, hs.refl _⟩
  aux_sep h := T.auxSlot_injective U (Prod.ext (T.aux_sep h.1) (U.aux_sep h.2))
  aux_label h := T.product_aux_label U h
  label_hit := by
    rintro (⟨x, y⟩ | ⟨x, y⟩)
    · obtain ⟨p, hp⟩ := U.label_hit y
      exact ⟨.inl (x, p), hr.refl _, hp⟩
    · obtain ⟨p, hp⟩ := T.label_hit x
      exact ⟨.inr (p, y), hp, hs.refl _⟩

private theorem profile_product (T : PortTuple r) (U : PortTuple s)
    (hr : Std.Refl r) (hs : Std.Refl s)
    (hr' : Std.Symm r) (hs' : Std.Symm s) :
    (T.product U hr hs hr' hs').profile = T.profile.star U.profile := by
  rw [BPZProfile.star_eq_mk]
  dsimp only [profile, product, ProductB, ProductP, ProductN, ProductA]
  simp only [Fintype.card_sum, Fintype.card_prod, Nat.cast_add, Nat.cast_mul]
  congr 1 <;> ring

end Product
end PortTuple

/-- The 148 starting codewords, as base-11 encodings of length-three words. -/
def bpzC11BaseWords : List (Fin 1331) :=
  [
    5, 7, 11, 26, 28, 43, 47, 49, 64, 69, 86, 90, 107, 111,
    130, 134, 151, 155, 172, 177, 192, 194, 198, 213, 215, 230, 234, 242,
    257, 259, 274, 278, 280, 295, 300, 317, 321, 338, 342, 357, 359, 365,
    382, 386, 403, 407, 423, 425, 429, 444, 446, 461, 465, 482, 488, 490,
    505, 509, 511, 526, 530, 548, 552, 569, 573, 588, 590, 594, 613, 617,
    634, 638, 653, 655, 660, 675, 677, 692, 696, 713, 717, 732, 740, 747,
    753, 761, 768, 783, 789, 804, 811, 819, 825, 832, 840, 855, 859, 876,
    880, 895, 897, 912, 917, 919, 934, 938, 955, 959, 978, 982, 984, 999,
    1003, 1020, 1024, 1042, 1046, 1061, 1063, 1067, 1082, 1084, 1090, 1107, 1111, 1126,
    1128, 1143, 1147, 1149, 1165, 1169, 1186, 1190, 1207, 1213, 1230, 1234, 1251, 1255,
    1272, 1277, 1292, 1294, 1298, 1313, 1315, 1330
  ]

/-- The 148 auxiliary words, in the same base-11 encoding. -/
def bpzC11AuxWords : List (Fin 1331) :=
  [
    10, 19, 28, 37, 46, 55, 63, 72, 81, 90, 99, 108, 117, 122,
    126, 135, 144, 162, 164, 171, 180, 189, 198, 207, 216, 225, 234, 261,
    263, 270, 279, 288, 297, 306, 315, 324, 333, 342, 360, 362, 365, 369,
    378, 387, 396, 405, 414, 423, 432, 441, 459, 461, 468, 477, 495, 504,
    513, 522, 531, 540, 558, 560, 567, 576, 585, 594, 603, 608, 612, 621,
    630, 639, 657, 659, 666, 675, 684, 693, 702, 711, 720, 738, 756, 758,
    765, 774, 783, 792, 801, 810, 819, 828, 837, 846, 851, 855, 864, 873,
    882, 891, 900, 909, 918, 927, 936, 945, 954, 963, 968, 981, 990, 999,
    1008, 1017, 1026, 1035, 1044, 1053, 1062, 1071, 1080, 1094, 1098, 1107, 1116, 1125,
    1134, 1143, 1152, 1161, 1170, 1179, 1188, 1197, 1206, 1211, 1224, 1233, 1242, 1251,
    1260, 1269, 1278, 1287, 1296, 1305, 1314, 1323
  ]

/-- The three starting ports, with each parent first and alternative second. -/
def bpzC11Ports : List (Fin 1331 × Fin 1331) :=
  [(5, 1215), (64, 65), (747, 736)]

private def Confusable {q n : ℕ} (a b : Fin n → ZMod q) : Prop :=
  ∀ i, a i - b i = -1 ∨ a i - b i = 0 ∨ a i - b i = 1

private instance {q n : ℕ} : DecidableRel (@Confusable q n) := fun a b =>
  inferInstanceAs (Decidable (∀ i, a i - b i = -1 ∨ a i - b i = 0 ∨ a i - b i = 1))

private theorem confusable_refl {q n : ℕ} : Std.Refl (@Confusable q n) :=
  ⟨fun _ _ => Or.inr (Or.inl (sub_self _))⟩

private theorem confusable_symm {q n : ℕ} : Std.Symm (@Confusable q n) := by
  constructor
  intro a b h i
  rw [← neg_sub]
  rcases h i with hi | hi | hi <;> simp [hi]

/-- Decode the three base-11 digits of an encoded word, least significant digit first. -/
def bpzC11Decode (a : Fin 1331) (i : Fin 3) : ZMod 11 := (a.val / 11 ^ i.val : ℕ)

private abbrev rawConf (a b : Fin 1331) : Prop := Confusable (bpzC11Decode a) (bpzC11Decode b)

private def rawEnd (c : Bool) (p : Fin 1331 × Fin 1331) : Fin 1331 :=
  if c then p.2 else p.1

private def rawFoot (c : Bool) (x : Fin 1331) : Bool :=
  bpzC11Ports.any fun p => decide (rawConf x (rawEnd c p))

private def rawActive (x : Fin 1331) : Bool := rawFoot false x || rawFoot true x

private def coreWords : List (Fin 1331) :=
  bpzC11BaseWords.filter fun x => !(bpzC11Ports.any fun p => p.1 == x)

private def neutralWords : List (Fin 1331) := bpzC11AuxWords.filter fun x => !rawActive x

private def activeWords : List (Fin 1331) := bpzC11AuxWords.filter rawActive

set_option maxRecDepth 4096 in
private theorem coreSepCheck : coreWords.Pairwise (fun a b => ¬ rawConf a b) := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem auxSepCheck : bpzC11AuxWords.Pairwise (fun a b => ¬ rawConf a b) := by
  decide +kernel

private theorem corePortCheck :
    coreWords.all (fun x => bpzC11Ports.all fun p =>
      decide (¬ rawConf x p.1 ∧ ¬ rawConf x p.2)) = true := by
  decide +kernel

private theorem portsSepCheck : bpzC11Ports.Pairwise (fun p q =>
    ∀ b c : Bool, ¬ rawConf (rawEnd b p) (rawEnd c q)) := by
  decide +kernel

private theorem endsCheck : bpzC11Ports.all (fun p =>
    decide (bpzC11Decode p.1 ≠ bpzC11Decode p.2 ∧ rawConf p.1 p.2)) = true := by
  decide +kernel

private theorem footCheck :
    bpzC11AuxWords.all (fun x => !(rawFoot false x && rawFoot true x)) = true := by
  decide +kernel

private theorem eq_index_of_confusable {α : Type} {l : List α} {r : α → α → Prop}
    (hs : Std.Symm r) (hp : l.Pairwise (fun x y => ¬ r x y)) {i j : Fin l.length}
    (h : r l[i] l[j]) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim (List.pairwise_iff_getElem.mp hp i j i.isLt j.isLt hij h)
  · exact hij
  · exact False.elim (List.pairwise_iff_getElem.mp hp j i j.isLt i.isLt hji (hs.symm _ _ h))

private theorem rawConf_symm : Std.Symm rawConf := ⟨fun _ _ h => confusable_symm.symm _ _ h⟩

private theorem raw_eq_of_confusable {x y : Fin 1331} (hx : x ∈ bpzC11AuxWords)
    (hy : y ∈ bpzC11AuxWords) (h : rawConf x y) : x = y := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hy
  exact congrArg bpzC11AuxWords.get (eq_index_of_confusable rawConf_symm auxSepCheck h)

private def auxSource : Fin neutralWords.length ⊕ Fin activeWords.length → Fin 1331 :=
  Sum.elim neutralWords.get activeWords.get

private theorem auxSource_mem (i : Fin neutralWords.length ⊕ Fin activeWords.length) :
    auxSource i ∈ bpzC11AuxWords := by
  rcases i with i | i
  · exact List.mem_of_mem_filter (List.get_mem _ _)
  · exact List.mem_of_mem_filter (List.get_mem _ _)

private theorem auxSource_neutral (i : Fin neutralWords.length) :
    rawActive (auxSource (.inl i)) = false := by
  have h := (List.mem_filter.mp (List.get_mem neutralWords i : _ ∈ neutralWords)).2
  simpa only [auxSource, Sum.elim_inl, Bool.not_eq_true'] using h

private theorem auxSource_active (i : Fin activeWords.length) :
    rawActive (auxSource (.inr i)) = true :=
  (List.mem_filter.mp (List.get_mem activeWords i : _ ∈ activeWords)).2

private theorem auxSource_sep {i j : Fin neutralWords.length ⊕ Fin activeWords.length}
    (h : rawConf (auxSource i) (auxSource j)) : i = j := by
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (eq_index_of_confusable rawConf_symm (auxSepCheck.filter _) h)
  · have e := raw_eq_of_confusable (auxSource_mem (.inl i)) (auxSource_mem (.inr j)) h
    have hi := auxSource_neutral i
    rw [e, auxSource_active] at hi
    contradiction
  · have e := raw_eq_of_confusable (auxSource_mem (.inr i)) (auxSource_mem (.inl j)) h
    have hi := auxSource_active i
    rw [e, auxSource_neutral] at hi
    contradiction
  · exact congrArg Sum.inr (eq_index_of_confusable rawConf_symm (auxSepCheck.filter _) h)

private theorem rawFoot_of_conf {c : Bool} {x : Fin 1331} {p : Fin bpzC11Ports.length}
    (h : rawConf x (rawEnd c bpzC11Ports[p])) : rawFoot c x = true :=
  List.any_eq_true.mpr ⟨_, List.get_mem _ p, decide_eq_true h⟩

private theorem exists_conf_of_rawFoot {c : Bool} {x : Fin 1331} (h : rawFoot c x = true) :
    ∃ p : Fin bpzC11Ports.length, rawConf x (rawEnd c bpzC11Ports[p]) := by
  obtain ⟨p, hp, hc⟩ := List.any_eq_true.mp h
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
  exact ⟨i, of_decide_eq_true hc⟩

private def c11BaseTuple : PortTuple (@Confusable 11 3) where
  B := Fin coreWords.length
  P := Fin bpzC11Ports.length
  N := Fin neutralWords.length
  A := Fin activeWords.length
  finiteB := inferInstance
  finiteP := inferInstance
  finiteN := inferInstance
  finiteA := inferInstance
  core i := bpzC11Decode coreWords[i]
  endpoint c p := bpzC11Decode (rawEnd c bpzC11Ports[p])
  side _ := false
  aux i := bpzC11Decode (auxSource i)
  label i := rawFoot true activeWords[i]
  core_sep h := eq_index_of_confusable rawConf_symm coreSepCheck h
  core_port i p c h := by
    have hc := List.all_eq_true.mp corePortCheck _ (List.get_mem coreWords i)
    have hp := of_decide_eq_true (List.all_eq_true.mp hc _ (List.get_mem bpzC11Ports p))
    cases c
    · exact hp.1 h
    · exact hp.2 h
  ports_sep := by
    intro p q b c h
    rcases lt_trichotomy p q with hpq | hpq | hqp
    · exact False.elim (List.pairwise_iff_getElem.mp portsSepCheck p q p.isLt q.isLt hpq b c h)
    · exact hpq
    · exact False.elim (List.pairwise_iff_getElem.mp portsSepCheck q p q.isLt p.isLt hqp c b
        (rawConf_symm.symm _ _ h))
  ends_ne p := (of_decide_eq_true (List.all_eq_true.mp endsCheck _ (List.get_mem bpzC11Ports p))).1
  ends_rel p := (of_decide_eq_true (List.all_eq_true.mp endsCheck _ (List.get_mem bpzC11Ports p))).2
  aux_sep h := auxSource_sep h
  aux_label := by
    intro x p c h
    have hf := rawFoot_of_conf h
    rcases x with i | i
    · have hn := auxSource_neutral i
      cases c <;> simp [rawActive, hf] at hn
    · cases c
      · have hh := List.all_eq_true.mp footCheck _ (auxSource_mem (.inr i))
        have hLabel : rawFoot true (auxSource (.inr i)) = false := by
          simpa [hf] using hh
        exact congrArg some hLabel
      · exact congrArg some hf
  label_hit i := by
    change ∃ p : Fin bpzC11Ports.length,
      rawConf (auxSource (.inr i)) (rawEnd (rawFoot true (auxSource (.inr i))) bpzC11Ports[p])
    cases h : rawFoot true (auxSource (.inr i))
    · apply exists_conf_of_rawFoot
      simpa [rawActive, h] using auxSource_active i
    · exact exists_conf_of_rawFoot h

private def appendWords {q m n : ℕ} :
    ((Fin m → ZMod q) × (Fin n → ZMod q)) ↪ (Fin (m + n) → ZMod q) :=
  ((Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) (ZMod q)).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _))).toEmbedding

private theorem confusable_appendWords {q m n : ℕ} (x y : (Fin m → ZMod q) × (Fin n → ZMod q)) :
    Confusable (appendWords x) (appendWords y) ↔
      PortTuple.pairRel Confusable Confusable x y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  constructor
  · intro h
    exact ⟨fun i => by simpa [appendWords, Equiv.arrowCongr] using h (finSumFinEquiv (.inl i)),
      fun i => by simpa [appendWords, Equiv.arrowCongr] using h (finSumFinEquiv (.inr i))⟩
  · intro h k
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
    · simpa [appendWords, Equiv.arrowCongr] using h.1 i
    · simpa [appendWords, Equiv.arrowCongr] using h.2 i

private def HasProfile (q n : ℕ) (p : BPZProfile) : Prop :=
  ∃ T : PortTuple (@Confusable q n), T.profile = p

private theorem HasProfile.star {q m n : ℕ} {p p' : BPZProfile}
    (h : HasProfile q m p) (h' : HasProfile q n p') : HasProfile q (m + n) (p.star p') := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨U, hU⟩ := h'
  let V := T.product U confusable_refl confusable_refl confusable_symm confusable_symm
  refine ⟨V.map appendWords confusable_appendWords, ?_⟩
  rw [PortTuple.profile_map, PortTuple.profile_product, hT, hU]

attribute [local instance] PortTuple.finiteB PortTuple.finiteP

private theorem HasProfile.exists_code {q n : ℕ} {p : BPZProfile} (h : HasProfile q n p) :
    ∃ C : Finset (Fin n → ZMod q), IsCycleCode q C ∧ C.card = p.code.toNat := by
  obtain ⟨T, rfl⟩ := h
  let e : T.B ⊕ T.P ↪ (Fin n → ZMod q) :=
    ⟨T.word, fun _ _ h => T.word_sep confusable_symm (h ▸ confusable_refl.refl _)⟩
  refine ⟨Finset.univ.map e, isCycleCode_iff_eq_of_confusable.mpr ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hb
    exact congrArg e (T.word_sep confusable_symm hab)
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_sum]
    simp only [PortTuple.profile, ← Nat.cast_add, Int.toNat_natCast]

/-- **One-block BPZ profile for the 11-cycle.** The one-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile with code coordinate $148$, pairs coordinate $3$, auxiliary
coordinate $148$ and neutral coordinate $142$.

This is the profile of the dimension-$3$ starting tuple.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi1 : BPZProfile := ⟨148, 3, 148, 142⟩
/-- **Two-block BPZ profile for the 11-cycle.** The two-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile product $\pi_1 \star \pi_1$, where $\pi_1$ is their one-block
eleven-cycle profile.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi2 : BPZProfile := bpzC11Pi1.star bpzC11Pi1
/-- **Three-block BPZ profile for the 11-cycle.** The three-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile product $\pi_1 \star \pi_2$, where $\pi_1$ and $\pi_2$ are
their one-block and two-block eleven-cycle profiles.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi3 : BPZProfile := bpzC11Pi1.star bpzC11Pi2
/-- **Four-block BPZ profile for the 11-cycle.** The four-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile product $\pi_2 \star \pi_2$, where $\pi_2$ is their two-block
eleven-cycle profile.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi4 : BPZProfile := bpzC11Pi2.star bpzC11Pi2
/-- **Seven-block BPZ profile for the 11-cycle.** The seven-block eleven-cycle profile of Buys,
Polak and Zuiddam is the profile product $\pi_3 \star \pi_4$, where $\pi_3$ and $\pi_4$ are
their three-block and four-block eleven-cycle profiles.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi7 : BPZProfile := bpzC11Pi3.star bpzC11Pi4
/-- **Eight-block BPZ profile of the eleven-cycle.** The eight-block BPZ profile of the
eleven-cycle is $\pi_4 \star \pi_4$, where $\pi_4$ is the four-block BPZ profile of the
eleven-cycle and $\star$ is the BPZ profile product.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi8 : BPZProfile := bpzC11Pi4.star bpzC11Pi4
/-- **Fourteen-block BPZ profile for the 11-cycle.** The fourteen-block eleven-cycle profile of
Buys, Polak and Zuiddam is the profile product $\pi_7 \star \pi_7$, where $\pi_7$ is their
seven-block eleven-cycle profile.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi14 : BPZProfile := bpzC11Pi7.star bpzC11Pi7
/-- **Fifteen-block BPZ profile for the 11-cycle.** The fifteen-block eleven-cycle profile of
Buys, Polak and Zuiddam is the profile product $\pi_7 \star \pi_8$, where $\pi_7$ and $\pi_8$
are their seven-block and eight-block eleven-cycle profiles.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi15 : BPZProfile := bpzC11Pi7.star bpzC11Pi8
/-- **Twenty-nine-block BPZ profile for the 11-cycle.** The twenty-nine-block eleven-cycle
profile of Buys, Polak and Zuiddam is the profile product $\pi_{14} \star \pi_{15}$, where
$\pi_{14}$ and $\pi_{15}$ are their fourteen-block and fifteen-block eleven-cycle profiles.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi29 : BPZProfile := bpzC11Pi14.star bpzC11Pi15
/-- **Fifty-eight-block BPZ profile for the 11-cycle.** The final fifty-eight-block eleven-cycle
profile of Buys, Polak and Zuiddam is the profile product $\pi_{29} \star \pi_{29}$, where
$\pi_{29}$ is their twenty-nine-block eleven-cycle profile.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction. -/
def bpzC11Pi58 : BPZProfile := bpzC11Pi29.star bpzC11Pi29

set_option maxRecDepth 4096 in
private theorem c11Profile1 : HasProfile 11 3 bpzC11Pi1 :=
  ⟨c11BaseTuple, by decide +kernel⟩

private theorem c11Profile58 : HasProfile 11 174 bpzC11Pi58 := by
  have h₂ : HasProfile 11 6 bpzC11Pi2 := c11Profile1.star c11Profile1
  have h₃ : HasProfile 11 9 bpzC11Pi3 := c11Profile1.star h₂
  have h₄ : HasProfile 11 12 bpzC11Pi4 := h₂.star h₂
  have h₇ : HasProfile 11 21 bpzC11Pi7 := h₃.star h₄
  have h₈ : HasProfile 11 24 bpzC11Pi8 := h₄.star h₄
  have h₁₄ : HasProfile 11 42 bpzC11Pi14 := h₇.star h₇
  have h₁₅ : HasProfile 11 45 bpzC11Pi15 := h₇.star h₈
  have h₂₉ : HasProfile 11 87 bpzC11Pi29 := h₁₄.star h₁₅
  exact h₂₉.star h₂₉

/-- **Buys–Polak–Zuiddam code for the eleven-cycle in dimension 174.** Let $c$ be the code
coordinate of the fifty-eight-block eleven-cycle profile $\pi_{58}$ of Buys–Polak–Zuiddam. There
is a finite set of words of length $174$ over $\mathbb{Z}/11\mathbb{Z}$ that is an independent
code for the $11$-cycle and has exactly $\max(c, 0)$ elements.

Source: BPZ, arXiv:2607.29681, eleven-cycle construction in dimension 174. -/
theorem bpz2026CycleElevenConstruction :
  ∃ A : Finset (Fin 174 → ZMod 11), IsCycleCode 11 A ∧ A.card = bpzC11Pi58.code.toNat :=
  c11Profile58.exists_code

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
