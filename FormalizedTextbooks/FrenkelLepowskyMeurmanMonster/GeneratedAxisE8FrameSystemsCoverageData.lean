/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsLabels

/-! Finite greedy-basis coverage checks for intrinsic maximal singular four-spaces.
Every numerical cache is checked by the ordinary Lean kernel. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The explicitly enumerated binary span of a finite list of root-coordinate labels. -/
def generatedAxisE8FrameSpanLabels : List (Fin 256) → Finset (Fin 256)
  | [] => {0}
  | a :: l => let S := generatedAxisE8FrameSpanLabels l
    S ∪ S.image (generatedAxisE8FrameLabelXor a)

/-- The greedy property: each basis label is the least label outside the preceding span. -/
def generatedAxisE8FrameCanonicalLabels (l : List (Fin 256)) : Prop :=
  ∀ i : Fin l.length, l[i] ∉ generatedAxisE8FrameSpanLabels (l.take i.val) ∧
    ∀ x ∈ generatedAxisE8FrameSpanLabels l,
      x ∉ generatedAxisE8FrameSpanLabels (l.take i.val) → l[i] ≤ x

/-- A duplicate-tolerant xor-span list, used for compact finite checking. -/
def generatedAxisE8FrameSpanLabelList : List (Fin 256) → List (Fin 256)
  | [] => [0]
  | a :: l => let S := generatedAxisE8FrameSpanLabelList l
    S ++ S.map (generatedAxisE8FrameLabelXor a)

/-- A Boolean greedy check avoids constructing large decidability proof terms. -/
def generatedAxisE8FrameAdmissibleCheck (l : List (Fin 256)) : Bool :=
  let S := generatedAxisE8FrameSpanLabelList l
  S.all (fun x => generatedAxisE8FrameSingularMask.testBit x.val) &&
  (List.range l.length).all (fun i =>
    let T := generatedAxisE8FrameSpanLabelList (l.take i)
    !T.contains l[i]! && S.all (fun x => T.contains x || decide (l[i]! ≤ x)))

/-- Greedy independent labels whose entire binary span is intrinsically singular. -/
def generatedAxisE8FrameAdmissibleLabels (l : List (Fin 256)) : Prop :=
  generatedAxisE8FrameAdmissibleCheck l = true

instance generatedAxisE8FrameAdmissibleLabelsDecidable (l : List (Fin 256)) :
    Decidable (generatedAxisE8FrameAdmissibleLabels l) := inferInstanceAs
      (Decidable (generatedAxisE8FrameAdmissibleCheck l = true))

/-- A four-byte numerical tag, with the first greedy basis label as the highest byte. -/
def generatedAxisE8FrameBasisTag (a b c d : Fin 256) : ℕ :=
  a.val * 16777216 + b.val * 65536 + c.val * 256 + d.val

set_option maxRecDepth 10000 in
-- The270 distinct canonical basis tags form a nested finite array literal.
/-- The sorted canonical four-byte tags of the displayed candidate bases. -/
def generatedAxisE8FrameCandidateTags : Array ℕ :=
  #[
    119089729, 119089857, 119089985, 119090113, 119106177, 119106433, 119155009, 119155137,
    119155521, 119155649, 119171202, 119171714, 119220545, 119220673, 119220801, 119220929,
    119236739, 119237507, 120150657, 120150913, 120215682, 120216194, 120281219, 120281987,
    120674945, 120675201, 120739970, 120740482, 120805507, 120806275, 185935425, 185935553,
    185935681, 185935809, 185951873, 185952129, 186000705, 186000833, 186001217, 186001345,
    186016898, 186017410, 186066241, 186066369, 186066497, 186066625, 186082435, 186083203,
    186996353, 186996609, 187061378, 187061890, 187126915, 187127683, 187782785, 187783041,
    187847810, 187848322, 187913347, 187914115, 219358785, 219358913, 219359041, 219359169,
    219375233, 219375489, 219554625, 219554753, 219555649, 219555777, 219570820, 219571844,
    219620161, 219620289, 219620929, 219621057, 219636357, 219637637, 220419713, 220419969,
    220615300, 220616324, 220680837, 220682117, 221337217, 221337473, 221532804, 221533828,
    221598341, 221599621, 236135745, 236135873, 236136257, 236136385, 236151938, 236152450,
    236266305, 236266433, 236267329, 236267457, 236282500, 236283524, 236397377, 236397505,
    236397889, 236398017, 236413574, 236414086, 237196418, 237196930, 237326980, 237328004,
    237458054, 237458566, 238179458, 238179970, 238310020, 238311044, 238441094, 238441606,
    252912961, 252913089, 252913217, 252913345, 252929155, 252929923, 253043521, 253043649,
    253044289, 253044417, 253059717, 253060997, 253109057, 253109185, 253109569, 253109697,
    253125254, 253125766, 253973635, 253974403, 254104197, 254105477, 254169734, 254170246,
    255022211, 255022979, 255152773, 255154053, 255218310, 255218822, 321212033, 321212289,
    321277058, 321277570, 321342595, 321343363, 321474177, 321474433, 321539202, 321539714,
    321604739, 321605507, 354635393, 354635649, 354830980, 354832004, 354896517, 354897797,
    355028609, 355028865, 355224196, 355225220, 355289733, 355291013, 371412098, 371412610,
    371542660, 371543684, 371673734, 371674246, 371870850, 371871362, 372001412, 372002436,
    372132486, 372132998, 388189315, 388190083, 388319877, 388321157, 388385414, 388385926,
    388713603, 388714371, 388844165, 388845445, 388909702, 388910214, 421744257, 421744513,
    421875329, 421875585, 422200968, 422203016, 422266505, 422268809, 422332040, 422334088,
    422397577, 422399881, 438520962, 438521474, 438717570, 438718082, 438912648, 438914696,
    439043722, 439045258, 439109256, 439111304, 439240330, 439241866, 455298179, 455298947,
    455560323, 455561091, 455689865, 455692169, 455755402, 455756938, 455952009, 455954313,
    456017546, 456019082, 472205956, 472206980, 472271492, 472272516, 472467080, 472469128,
    472532616, 472534664, 472729228, 472730252, 472794764, 472795788, 488983173, 488984453,
    489114245, 489115525, 489244297, 489246601, 489375369, 489377673, 489440908, 489441932,
    489571980, 489573004, 505825926, 505826438, 505891462, 505891974, 506087050, 506088586,
    506152586, 506154122, 506218124, 506219148, 506283660, 506284684]

/-- A bounded binary search on the sorted candidate tags. -/
def generatedAxisE8FrameCandidateSearch : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | fuel + 1, lo, hi, tag =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let v := generatedAxisE8FrameCandidateTags[mid]!
      if v = tag then mid else if tag < v then
        generatedAxisE8FrameCandidateSearch fuel lo mid tag
      else generatedAxisE8FrameCandidateSearch fuel (mid + 1) hi tag
    else 0

/-- The candidate index found by a nine-level search through270 distinct tags. -/
def generatedAxisE8FrameCandidateIndex (a b c d : Fin 256) : Fin 270 :=
  ⟨generatedAxisE8FrameCandidateSearch 9 0 270 (generatedAxisE8FrameBasisTag a b c d) % 270,
    Nat.mod_lt _ (by decide)⟩

/-- The compact finite coverage test for one fixed first greedy label. -/
def generatedAxisE8FrameCandidateCoverageAt (a : Fin 256) : Prop :=
  generatedAxisE8FrameAdmissibleLabels [a] →
  ∀ b : Fin 256, generatedAxisE8FrameAdmissibleLabels [a, b] →
  ∀ c : Fin 256, generatedAxisE8FrameAdmissibleLabels [a, b, c] →
  ∀ d : Fin 256, generatedAxisE8FrameAdmissibleLabels [a, b, c, d] →
    generatedAxisE8FrameCandidateTags[(generatedAxisE8FrameCandidateIndex a b c d).val]! =
      generatedAxisE8FrameBasisTag a b c d

instance generatedAxisE8FrameCandidateCoverageAtDecidable (a : Fin 256) :
    Decidable (generatedAxisE8FrameCandidateCoverageAt a) := by
  unfold generatedAxisE8FrameCandidateCoverageAt
  infer_instance

/-- An explicit Boolean search rejects false prefixes before visiting later labels. -/
def generatedAxisE8FrameCandidateCoverageCheckAt (a : Fin 256) : Bool :=
  if generatedAxisE8FrameAdmissibleCheck [a] then
    (List.finRange 256).all (fun b =>
      if generatedAxisE8FrameAdmissibleCheck [a, b] then
        (List.finRange 256).all (fun c =>
          if generatedAxisE8FrameAdmissibleCheck [a, b, c] then
            (List.finRange 256).all (fun d =>
              if generatedAxisE8FrameAdmissibleCheck [a, b, c, d] then
                generatedAxisE8FrameCandidateTags[
                  (generatedAxisE8FrameCandidateIndex a b c d).val]! ==
                    generatedAxisE8FrameBasisTag a b c d
              else true)
          else true)
      else true)
  else true

/-- A checked Boolean search proves the unchanged ordinary greedy-basis coverage contract. -/
theorem generatedAxisE8FrameCandidateCoverage_of_check (a : Fin 256)
    (h : generatedAxisE8FrameCandidateCoverageCheckAt a = true) :
    generatedAxisE8FrameCandidateCoverageAt a := by
  intro ha b hb c hc d hd
  change generatedAxisE8FrameAdmissibleCheck [a] = true at ha
  change generatedAxisE8FrameAdmissibleCheck [a, b] = true at hb
  change generatedAxisE8FrameAdmissibleCheck [a, b, c] = true at hc
  change generatedAxisE8FrameAdmissibleCheck [a, b, c, d] = true at hd
  unfold generatedAxisE8FrameCandidateCoverageCheckAt at h
  rw [ha] at h
  simp only [ite_true] at h
  have hB := List.all_eq_true.mp h b (List.mem_finRange b)
  rw [hb] at hB
  simp only [ite_true] at hB
  have hC := List.all_eq_true.mp hB c (List.mem_finRange c)
  rw [hc] at hC
  simp only [ite_true] at hC
  have hD := List.all_eq_true.mp hC d (List.mem_finRange d)
  rw [hd] at hD
  simpa only [ite_true, beq_iff_eq] using hD

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
