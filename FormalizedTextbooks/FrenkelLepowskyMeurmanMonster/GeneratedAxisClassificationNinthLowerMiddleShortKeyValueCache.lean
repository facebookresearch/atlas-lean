/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortData

/-! Exact key and value tree maps avoid repeatedly decoding original entry indices. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- A source search tree retains the complete numerical key and integer value at every node. -/
inductive GeneratedNinthIncomingValueTree where
  /-- No original entry remains in this subtree. -/
  | empty : GeneratedNinthIncomingValueTree
  /-- One original key and value with both original source subtrees. -/
  | node (key : ℕ) (value : ℤ) (left right : GeneratedNinthIncomingValueTree) :
      GeneratedNinthIncomingValueTree

/-- Search the complete cached tree by the same original source address. -/
def GeneratedNinthIncomingValueTree.lookup (t : GeneratedNinthIncomingValueTree) (q : ℕ) : ℤ :=
  match t with
  | .empty => 0
  | .node key value left right =>
      if q = key then value else if q < key then left.lookup q else right.lookup q

/-- Map every original index node to its complete original numerical key and value. -/
def GeneratedNinthIncomingTree.mapKeyValue {ι : Type*} (key : ι → ℕ) (value : ι → ℤ) :
    GeneratedNinthIncomingTree ι → GeneratedNinthIncomingValueTree
  | .empty => .empty
  | .node i left right => .node (key i) (value i)
      (left.mapKeyValue key value) (right.mapKeyValue key value)

/-- Mapping the entire source tree preserves its exact answer for every numerical query. -/
theorem GeneratedNinthIncomingTree.lookup_mapKeyValue {ι : Type*}
    (key : ι → ℕ) (value : ι → ℤ) (t : GeneratedNinthIncomingTree ι) (q : ℕ) :
    (t.mapKeyValue key value).lookup q =
      match t.lookup key q with
      | none => 0
      | some i => value i := by
  induction t with
  | empty => rfl
  | node i left right ihl ihr =>
      by_cases hq : q = key i
      · simp only [mapKeyValue, GeneratedNinthIncomingValueTree.lookup,
          GeneratedNinthIncomingTree.lookup, hq, ite_true]
      · by_cases hl : q < key i
        · simp only [mapKeyValue, GeneratedNinthIncomingValueTree.lookup,
            GeneratedNinthIncomingTree.lookup, hq, hl, ite_false, ite_true, ihl]
        · simp only [mapKeyValue, GeneratedNinthIncomingValueTree.lookup,
            GeneratedNinthIncomingTree.lookup, hq, hl, ite_false, ihr]

/-- All3856 original entries, with both original source subtrees and complete signed values. -/
def generatedNinthLowerMiddleShortKeyValueTree : GeneratedNinthIncomingValueTree :=
  (.node 49247 (-2)
    (.node 24667 (-2)
      (.node 11823 (-2)
        (.node 6102 (2)
          (.node 3315 (-2)
            (.node 1903 (-2)
              (.node 1128 (2)
                (.node 709 (2)
                  (.node 507 (2)
                    (.node 267 (-2)
                      (.node 46 (-2)
                        (.node 37 (-2)
                          .empty
                          .empty)
                        (.node 154 (-2)
                          .empty
                          .empty))
                      (.node 409 (2)
                        (.node 298 (2)
                          .empty
                          .empty)
                        (.node 463 (2)
                          .empty
                          .empty)))
                    (.node 636 (-2)
                      (.node 579 (-2)
                        (.node 552 (2)
                          .empty
                          .empty)
                        (.node 626 (-2)
                          .empty
                          .empty))
                      (.node 672 (2)
                        (.node 654 (-2)
                          .empty
                          .empty)
                        (.node 697 (2)
                          .empty
                          .empty))))
                  (.node 918 (2)
                    (.node 827 (-2)
                      (.node 753 (2)
                        (.node 745 (-2)
                          .empty
                          .empty)
                        (.node 814 (-2)
                          .empty
                          .empty))
                      (.node 870 (2)
                        (.node 851 (-2)
                          .empty
                          .empty)
                        (.node 906 (2)
                          .empty
                          .empty)))
                    (.node 1033 (2)
                      (.node 975 (-2)
                        (.node 939 (-2)
                          .empty
                          .empty)
                        (.node 1009 (-2)
                          .empty
                          .empty))
                      (.node 1112 (-2)
                        (.node 1079 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 1499 (2)
                  (.node 1296 (2)
                    (.node 1226 (2)
                      (.node 1166 (2)
                        (.node 1147 (-2)
                          .empty
                          .empty)
                        (.node 1181 (2)
                          .empty
                          .empty))
                      (.node 1262 (-2)
                        (.node 1238 (2)
                          .empty
                          .empty)
                        (.node 1284 (-2)
                          .empty
                          .empty)))
                    (.node 1388 (-2)
                      (.node 1354 (-2)
                        (.node 1306 (-2)
                          .empty
                          .empty)
                        (.node 1366 (-2)
                          .empty
                          .empty))
                      (.node 1480 (2)
                        (.node 1397 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 1699 (-2)
                    (.node 1605 (2)
                      (.node 1560 (2)
                        (.node 1550 (2)
                          .empty
                          .empty)
                        (.node 1593 (2)
                          .empty
                          .empty))
                      (.node 1663 (2)
                        (.node 1650 (-2)
                          .empty
                          .empty)
                        (.node 1678 (-2)
                          .empty
                          .empty)))
                    (.node 1813 (2)
                      (.node 1740 (2)
                        (.node 1708 (-2)
                          .empty
                          .empty)
                        (.node 1781 (-2)
                          .empty
                          .empty))
                      (.node 1846 (2)
                        (.node 1840 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 2517 (-2)
                (.node 2170 (2)
                  (.node 2070 (-2)
                    (.node 1976 (2)
                      (.node 1941 (2)
                        (.node 1913 (2)
                          .empty
                          .empty)
                        (.node 1955 (2)
                          .empty
                          .empty))
                      (.node 2026 (2)
                        (.node 1982 (2)
                          .empty
                          .empty)
                        (.node 2055 (-2)
                          .empty
                          .empty)))
                    (.node 2110 (2)
                      (.node 2089 (2)
                        (.node 2075 (-2)
                          .empty
                          .empty)
                        (.node 2100 (-2)
                          .empty
                          .empty))
                      (.node 2157 (2)
                        (.node 2115 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 2328 (2)
                    (.node 2279 (2)
                      (.node 2209 (-2)
                        (.node 2198 (2)
                          .empty
                          .empty)
                        (.node 2273 (2)
                          .empty
                          .empty))
                      (.node 2306 (2)
                        (.node 2281 (-2)
                          .empty
                          .empty)
                        (.node 2323 (2)
                          .empty
                          .empty)))
                    (.node 2456 (2)
                      (.node 2407 (-2)
                        (.node 2375 (2)
                          .empty
                          .empty)
                        (.node 2424 (-2)
                          .empty
                          .empty))
                      (.node 2499 (2)
                        (.node 2472 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 2849 (2)
                  (.node 2668 (2)
                    (.node 2554 (2)
                      (.node 2540 (-2)
                        (.node 2526 (-2)
                          .empty
                          .empty)
                        (.node 2551 (2)
                          .empty
                          .empty))
                      (.node 2633 (-2)
                        (.node 2561 (2)
                          .empty
                          .empty)
                        (.node 2639 (-2)
                          .empty
                          .empty)))
                    (.node 2795 (2)
                      (.node 2704 (-2)
                        (.node 2694 (2)
                          .empty
                          .empty)
                        (.node 2714 (2)
                          .empty
                          .empty))
                      (.node 2838 (2)
                        (.node 2812 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 3062 (-2)
                    (.node 2980 (-2)
                      (.node 2915 (2)
                        (.node 2862 (-2)
                          .empty
                          .empty)
                        (.node 2968 (-2)
                          .empty
                          .empty))
                      (.node 3035 (-2)
                        (.node 3018 (-2)
                          .empty
                          .empty)
                        (.node 3050 (-2)
                          .empty
                          .empty)))
                    (.node 3219 (-2)
                      (.node 3124 (-2)
                        (.node 3112 (-2)
                          .empty
                          .empty)
                        (.node 3187 (2)
                          .empty
                          .empty))
                      (.node 3271 (-2)
                        (.node 3254 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 4665 (-2)
              (.node 4004 (-2)
                (.node 3701 (2)
                  (.node 3487 (-2)
                    (.node 3393 (2)
                      (.node 3350 (2)
                        (.node 3322 (-2)
                          .empty
                          .empty)
                        (.node 3359 (-2)
                          .empty
                          .empty))
                      (.node 3438 (2)
                        (.node 3425 (-2)
                          .empty
                          .empty)
                        (.node 3443 (-2)
                          .empty
                          .empty)))
                    (.node 3585 (-2)
                      (.node 3519 (2)
                        (.node 3490 (-2)
                          .empty
                          .empty)
                        (.node 3555 (2)
                          .empty
                          .empty))
                      (.node 3630 (2)
                        (.node 3617 (2)
                          .empty
                          .empty)
                        (.node 3683 (-2)
                          .empty
                          .empty))))
                  (.node 3880 (-2)
                    (.node 3796 (2)
                      (.node 3724 (-2)
                        (.node 3704 (-2)
                          .empty
                          .empty)
                        (.node 3745 (-2)
                          .empty
                          .empty))
                      (.node 3824 (-2)
                        (.node 3798 (-2)
                          .empty
                          .empty)
                        (.node 3826 (2)
                          .empty
                          .empty)))
                    (.node 3952 (2)
                      (.node 3933 (-2)
                        (.node 3895 (2)
                          .empty
                          .empty)
                        (.node 3938 (-2)
                          .empty
                          .empty))
                      (.node 3981 (2)
                        (.node 3961 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 4334 (-2)
                  (.node 4152 (2)
                    (.node 4087 (-2)
                      (.node 4068 (-2)
                        (.node 4044 (-2)
                          .empty
                          .empty)
                        (.node 4072 (2)
                          .empty
                          .empty))
                      (.node 4130 (-2)
                        (.node 4125 (-2)
                          .empty
                          .empty)
                        (.node 4141 (-2)
                          .empty
                          .empty)))
                    (.node 4225 (-2)
                      (.node 4197 (2)
                        (.node 4176 (2)
                          .empty
                          .empty)
                        (.node 4201 (-2)
                          .empty
                          .empty))
                      (.node 4288 (-2)
                        (.node 4264 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 4523 (2)
                    (.node 4406 (-2)
                      (.node 4371 (2)
                        (.node 4345 (-2)
                          .empty
                          .empty)
                        (.node 4388 (-2)
                          .empty
                          .empty))
                      (.node 4476 (-2)
                        (.node 4440 (-2)
                          .empty
                          .empty)
                        (.node 4498 (-2)
                          .empty
                          .empty)))
                    (.node 4623 (2)
                      (.node 4557 (-2)
                        (.node 4536 (-2)
                          .empty
                          .empty)
                        (.node 4574 (-2)
                          .empty
                          .empty))
                      (.node 4656 (-2)
                        (.node 4647 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 5424 (2)
                (.node 5042 (2)
                  (.node 4794 (2)
                    (.node 4736 (-2)
                      (.node 4698 (2)
                        (.node 4691 (-2)
                          .empty
                          .empty)
                        (.node 4727 (-2)
                          .empty
                          .empty))
                      (.node 4771 (-2)
                        (.node 4756 (2)
                          .empty
                          .empty)
                        (.node 4792 (-2)
                          .empty
                          .empty)))
                    (.node 4919 (2)
                      (.node 4899 (-2)
                        (.node 4876 (2)
                          .empty
                          .empty)
                        (.node 4917 (-2)
                          .empty
                          .empty))
                      (.node 5031 (-2)
                        (.node 5013 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 5329 (2)
                    (.node 5203 (2)
                      (.node 5064 (2)
                        (.node 5051 (-2)
                          .empty
                          .empty)
                        (.node 5089 (2)
                          .empty
                          .empty))
                      (.node 5268 (2)
                        (.node 5212 (-2)
                          .empty
                          .empty)
                        (.node 5286 (2)
                          .empty
                          .empty)))
                    (.node 5399 (-2)
                      (.node 5353 (2)
                        (.node 5349 (2)
                          .empty
                          .empty)
                        (.node 5375 (2)
                          .empty
                          .empty))
                      (.node 5419 (2)
                        (.node 5409 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 5753 (-2)
                  (.node 5554 (-2)
                    (.node 5490 (-2)
                      (.node 5461 (2)
                        (.node 5454 (-2)
                          .empty
                          .empty)
                        (.node 5485 (2)
                          .empty
                          .empty))
                      (.node 5543 (-2)
                        (.node 5528 (-2)
                          .empty
                          .empty)
                        (.node 5549 (2)
                          .empty
                          .empty)))
                    (.node 5631 (-2)
                      (.node 5607 (-2)
                        (.node 5592 (-2)
                          .empty
                          .empty)
                        (.node 5611 (-2)
                          .empty
                          .empty))
                      (.node 5731 (-2)
                        (.node 5729 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 6001 (-2)
                    (.node 5888 (2)
                      (.node 5843 (-2)
                        (.node 5755 (-2)
                          .empty
                          .empty)
                        (.node 5854 (2)
                          .empty
                          .empty))
                      (.node 5950 (-2)
                        (.node 5922 (2)
                          .empty
                          .empty)
                        (.node 5971 (2)
                          .empty
                          .empty)))
                    (.node 6063 (2)
                      (.node 6039 (2)
                        (.node 6018 (-2)
                          .empty
                          .empty)
                        (.node 6052 (-2)
                          .empty
                          .empty))
                      (.node 6088 (-2)
                        (.node 6065 (2)
                          .empty
                          .empty)
                        .empty)))))))
          (.node 9139 (-2)
            (.node 7670 (-2)
              (.node 6918 (2)
                (.node 6461 (2)
                  (.node 6287 (2)
                    (.node 6204 (-2)
                      (.node 6159 (2)
                        (.node 6125 (2)
                          .empty
                          .empty)
                        (.node 6187 (-2)
                          .empty
                          .empty))
                      (.node 6242 (2)
                        (.node 6229 (-2)
                          .empty
                          .empty)
                        (.node 6255 (-2)
                          .empty
                          .empty)))
                    (.node 6388 (2)
                      (.node 6364 (-2)
                        (.node 6316 (-2)
                          .empty
                          .empty)
                        (.node 6387 (2)
                          .empty
                          .empty))
                      (.node 6415 (2)
                        (.node 6408 (-2)
                          .empty
                          .empty)
                        (.node 6454 (-2)
                          .empty
                          .empty))))
                  (.node 6654 (-2)
                    (.node 6552 (-2)
                      (.node 6500 (-2)
                        (.node 6479 (-2)
                          .empty
                          .empty)
                        (.node 6504 (-2)
                          .empty
                          .empty))
                      (.node 6583 (2)
                        (.node 6570 (2)
                          .empty
                          .empty)
                        (.node 6635 (-2)
                          .empty
                          .empty)))
                    (.node 6816 (2)
                      (.node 6743 (2)
                        (.node 6703 (2)
                          .empty
                          .empty)
                        (.node 6768 (2)
                          .empty
                          .empty))
                      (.node 6887 (2)
                        (.node 6855 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 7356 (-2)
                  (.node 7115 (-2)
                    (.node 7027 (2)
                      (.node 6968 (2)
                        (.node 6923 (-2)
                          .empty
                          .empty)
                        (.node 7002 (2)
                          .empty
                          .empty))
                      (.node 7084 (-2)
                        (.node 7070 (-2)
                          .empty
                          .empty)
                        (.node 7095 (-2)
                          .empty
                          .empty)))
                    (.node 7273 (-2)
                      (.node 7213 (2)
                        (.node 7120 (2)
                          .empty
                          .empty)
                        (.node 7247 (2)
                          .empty
                          .empty))
                      (.node 7336 (-2)
                        (.node 7305 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 7518 (2)
                    (.node 7460 (-2)
                      (.node 7421 (2)
                        (.node 7406 (-2)
                          .empty
                          .empty)
                        (.node 7447 (-2)
                          .empty
                          .empty))
                      (.node 7488 (-2)
                        (.node 7467 (-2)
                          .empty
                          .empty)
                        (.node 7509 (-2)
                          .empty
                          .empty)))
                    (.node 7611 (-2)
                      (.node 7591 (-2)
                        (.node 7571 (-2)
                          .empty
                          .empty)
                        (.node 7600 (-2)
                          .empty
                          .empty))
                      (.node 7640 (2)
                        (.node 7635 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 8429 (-2)
                (.node 8071 (-2)
                  (.node 7850 (2)
                    (.node 7746 (2)
                      (.node 7701 (2)
                        (.node 7680 (2)
                          .empty
                          .empty)
                        (.node 7715 (2)
                          .empty
                          .empty))
                      (.node 7799 (-2)
                        (.node 7759 (-2)
                          .empty
                          .empty)
                        (.node 7834 (2)
                          .empty
                          .empty)))
                    (.node 7987 (2)
                      (.node 7934 (2)
                        (.node 7896 (-2)
                          .empty
                          .empty)
                        (.node 7972 (-2)
                          .empty
                          .empty))
                      (.node 8060 (2)
                        (.node 8035 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 8245 (2)
                    (.node 8160 (-2)
                      (.node 8096 (2)
                        (.node 8091 (2)
                          .empty
                          .empty)
                        (.node 8120 (-2)
                          .empty
                          .empty))
                      (.node 8227 (2)
                        (.node 8179 (2)
                          .empty
                          .empty)
                        (.node 8235 (2)
                          .empty
                          .empty)))
                    (.node 8359 (-2)
                      (.node 8258 (-2)
                        (.node 8252 (2)
                          .empty
                          .empty)
                        (.node 8311 (-2)
                          .empty
                          .empty))
                      (.node 8422 (2)
                        (.node 8404 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 8753 (-2)
                  (.node 8589 (-2)
                    (.node 8488 (2)
                      (.node 8472 (2)
                        (.node 8434 (2)
                          .empty
                          .empty)
                        (.node 8487 (2)
                          .empty
                          .empty))
                      (.node 8523 (-2)
                        (.node 8515 (-2)
                          .empty
                          .empty)
                        (.node 8544 (-2)
                          .empty
                          .empty)))
                    (.node 8693 (2)
                      (.node 8670 (-2)
                        (.node 8610 (2)
                          .empty
                          .empty)
                        (.node 8675 (-2)
                          .empty
                          .empty))
                      (.node 8750 (2)
                        (.node 8695 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 8993 (2)
                    (.node 8835 (2)
                      (.node 8807 (2)
                        (.node 8792 (2)
                          .empty
                          .empty)
                        (.node 8833 (-2)
                          .empty
                          .empty))
                      (.node 8900 (2)
                        (.node 8888 (2)
                          .empty
                          .empty)
                        (.node 8961 (-2)
                          .empty
                          .empty)))
                    (.node 9055 (-2)
                      (.node 9026 (-2)
                        (.node 9006 (2)
                          .empty
                          .empty)
                        (.node 9043 (-2)
                          .empty
                          .empty))
                      (.node 9110 (2)
                        (.node 9098 (2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 10436 (2)
              (.node 9705 (-2)
                (.node 9401 (-2)
                  (.node 9289 (-2)
                    (.node 9235 (-2)
                      (.node 9194 (-2)
                        (.node 9171 (2)
                          .empty
                          .empty)
                        (.node 9222 (2)
                          .empty
                          .empty))
                      (.node 9260 (-2)
                        (.node 9247 (-2)
                          .empty
                          .empty)
                        (.node 9281 (-2)
                          .empty
                          .empty)))
                    (.node 9340 (2)
                      (.node 9322 (2)
                        (.node 9316 (2)
                          .empty
                          .empty)
                        (.node 9335 (2)
                          .empty
                          .empty))
                      (.node 9390 (-2)
                        (.node 9345 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 9539 (-2)
                    (.node 9473 (-2)
                      (.node 9444 (2)
                        (.node 9427 (-2)
                          .empty
                          .empty)
                        (.node 9448 (2)
                          .empty
                          .empty))
                      (.node 9501 (2)
                        (.node 9492 (2)
                          .empty
                          .empty)
                        (.node 9515 (-2)
                          .empty
                          .empty)))
                    (.node 9639 (2)
                      (.node 9601 (-2)
                        (.node 9594 (2)
                          .empty
                          .empty)
                        (.node 9628 (2)
                          .empty
                          .empty))
                      (.node 9701 (-2)
                        (.node 9677 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 10014 (-2)
                  (.node 9839 (2)
                    (.node 9783 (-2)
                      (.node 9756 (2)
                        (.node 9716 (-2)
                          .empty
                          .empty)
                        (.node 9761 (-2)
                          .empty
                          .empty))
                      (.node 9812 (2)
                        (.node 9790 (2)
                          .empty
                          .empty)
                        (.node 9821 (2)
                          .empty
                          .empty)))
                    (.node 9897 (-2)
                      (.node 9868 (-2)
                        (.node 9840 (-2)
                          .empty
                          .empty)
                        (.node 9875 (-2)
                          .empty
                          .empty))
                      (.node 10004 (2)
                        (.node 9905 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 10235 (2)
                    (.node 10127 (-2)
                      (.node 10076 (-2)
                        (.node 10073 (2)
                          .empty
                          .empty)
                        (.node 10091 (-2)
                          .empty
                          .empty))
                      (.node 10215 (-2)
                        (.node 10152 (-2)
                          .empty
                          .empty)
                        (.node 10231 (-2)
                          .empty
                          .empty)))
                    (.node 10318 (2)
                      (.node 10274 (-2)
                        (.node 10254 (-2)
                          .empty
                          .empty)
                        (.node 10292 (2)
                          .empty
                          .empty))
                      (.node 10404 (-2)
                        (.node 10350 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 11123 (2)
                (.node 10758 (-2)
                  (.node 10611 (2)
                    (.node 10539 (2)
                      (.node 10489 (-2)
                        (.node 10451 (-2)
                          .empty
                          .empty)
                        (.node 10492 (2)
                          .empty
                          .empty))
                      (.node 10568 (-2)
                        (.node 10550 (2)
                          .empty
                          .empty)
                        (.node 10581 (2)
                          .empty
                          .empty)))
                    (.node 10707 (2)
                      (.node 10688 (2)
                        (.node 10614 (-2)
                          .empty
                          .empty)
                        (.node 10695 (-2)
                          .empty
                          .empty))
                      (.node 10732 (2)
                        (.node 10708 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 10981 (-2)
                    (.node 10796 (2)
                      (.node 10789 (2)
                        (.node 10767 (2)
                          .empty
                          .empty)
                        (.node 10793 (-2)
                          .empty
                          .empty))
                      (.node 10884 (-2)
                        (.node 10873 (-2)
                          .empty
                          .empty)
                        (.node 10973 (-2)
                          .empty
                          .empty)))
                    (.node 11011 (-2)
                      (.node 10998 (2)
                        (.node 10985 (2)
                          .empty
                          .empty)
                        (.node 11004 (2)
                          .empty
                          .empty))
                      (.node 11054 (-2)
                        (.node 11051 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 11471 (2)
                  (.node 11324 (2)
                    (.node 11228 (-2)
                      (.node 11193 (-2)
                        (.node 11126 (-2)
                          .empty
                          .empty)
                        (.node 11206 (-2)
                          .empty
                          .empty))
                      (.node 11268 (2)
                        (.node 11235 (2)
                          .empty
                          .empty)
                        (.node 11286 (-2)
                          .empty
                          .empty)))
                    (.node 11395 (-2)
                      (.node 11337 (-2)
                        (.node 11331 (-2)
                          .empty
                          .empty)
                        (.node 11350 (-2)
                          .empty
                          .empty))
                      (.node 11439 (-2)
                        (.node 11398 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 11648 (2)
                    (.node 11588 (-2)
                      (.node 11514 (-2)
                        (.node 11499 (2)
                          .empty
                          .empty)
                        (.node 11561 (-2)
                          .empty
                          .empty))
                      (.node 11608 (-2)
                        (.node 11605 (2)
                          .empty
                          .empty)
                        (.node 11633 (-2)
                          .empty
                          .empty)))
                    (.node 11763 (2)
                      (.node 11716 (-2)
                        (.node 11696 (-2)
                          .empty
                          .empty)
                        (.node 11758 (2)
                          .empty
                          .empty))
                      (.node 11797 (2)
                        (.node 11784 (-2)
                          .empty
                          .empty)
                        .empty))))))))
        (.node 18048 (2)
          (.node 14709 (-2)
            (.node 13216 (2)
              (.node 12503 (2)
                (.node 12123 (2)
                  (.node 11953 (2)
                    (.node 11883 (-2)
                      (.node 11860 (2)
                        (.node 11836 (2)
                          .empty
                          .empty)
                        (.node 11879 (2)
                          .empty
                          .empty))
                      (.node 11922 (2)
                        (.node 11884 (2)
                          .empty
                          .empty)
                        (.node 11925 (2)
                          .empty
                          .empty)))
                    (.node 12017 (2)
                      (.node 11976 (2)
                        (.node 11965 (-2)
                          .empty
                          .empty)
                        (.node 12004 (2)
                          .empty
                          .empty))
                      (.node 12110 (2)
                        (.node 12032 (-2)
                          .empty
                          .empty)
                        (.node 12117 (2)
                          .empty
                          .empty))))
                  (.node 12304 (2)
                    (.node 12209 (-2)
                      (.node 12190 (-2)
                        (.node 12128 (-2)
                          .empty
                          .empty)
                        (.node 12192 (2)
                          .empty
                          .empty))
                      (.node 12278 (2)
                        (.node 12257 (-2)
                          .empty
                          .empty)
                        (.node 12293 (-2)
                          .empty
                          .empty)))
                    (.node 12414 (-2)
                      (.node 12330 (-2)
                        (.node 12323 (2)
                          .empty
                          .empty)
                        (.node 12379 (-2)
                          .empty
                          .empty))
                      (.node 12499 (2)
                        (.node 12455 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 12877 (2)
                  (.node 12677 (2)
                    (.node 12587 (-2)
                      (.node 12573 (2)
                        (.node 12572 (-2)
                          .empty
                          .empty)
                        (.node 12586 (2)
                          .empty
                          .empty))
                      (.node 12662 (-2)
                        (.node 12648 (2)
                          .empty
                          .empty)
                        (.node 12667 (2)
                          .empty
                          .empty)))
                    (.node 12799 (-2)
                      (.node 12752 (2)
                        (.node 12743 (-2)
                          .empty
                          .empty)
                        (.node 12778 (2)
                          .empty
                          .empty))
                      (.node 12828 (2)
                        (.node 12809 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 12969 (2)
                    (.node 12924 (2)
                      (.node 12888 (2)
                        (.node 12883 (2)
                          .empty
                          .empty)
                        (.node 12902 (-2)
                          .empty
                          .empty))
                      (.node 12955 (2)
                        (.node 12935 (-2)
                          .empty
                          .empty)
                        (.node 12960 (2)
                          .empty
                          .empty)))
                    (.node 13139 (-2)
                      (.node 13036 (-2)
                        (.node 13001 (-2)
                          .empty
                          .empty)
                        (.node 13060 (-2)
                          .empty
                          .empty))
                      (.node 13190 (-2)
                        (.node 13154 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 13839 (-2)
                (.node 13480 (2)
                  (.node 13346 (-2)
                    (.node 13287 (-2)
                      (.node 13243 (2)
                        (.node 13238 (2)
                          .empty
                          .empty)
                        (.node 13258 (2)
                          .empty
                          .empty))
                      (.node 13304 (2)
                        (.node 13299 (2)
                          .empty
                          .empty)
                        (.node 13321 (2)
                          .empty
                          .empty)))
                    (.node 13395 (2)
                      (.node 13364 (2)
                        (.node 13359 (-2)
                          .empty
                          .empty)
                        (.node 13384 (2)
                          .empty
                          .empty))
                      (.node 13451 (-2)
                        (.node 13419 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 13676 (2)
                    (.node 13619 (2)
                      (.node 13559 (2)
                        (.node 13528 (2)
                          .empty
                          .empty)
                        (.node 13607 (2)
                          .empty
                          .empty))
                      (.node 13648 (-2)
                        (.node 13624 (2)
                          .empty
                          .empty)
                        (.node 13659 (2)
                          .empty
                          .empty)))
                    (.node 13776 (-2)
                      (.node 13741 (-2)
                        (.node 13684 (-2)
                          .empty
                          .empty)
                        (.node 13752 (2)
                          .empty
                          .empty))
                      (.node 13817 (-2)
                        (.node 13797 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 14317 (-2)
                  (.node 14080 (2)
                    (.node 13943 (2)
                      (.node 13881 (-2)
                        (.node 13880 (2)
                          .empty
                          .empty)
                        (.node 13929 (-2)
                          .empty
                          .empty))
                      (.node 13954 (2)
                        (.node 13948 (2)
                          .empty
                          .empty)
                        (.node 14065 (-2)
                          .empty
                          .empty)))
                    (.node 14200 (2)
                      (.node 14176 (2)
                        (.node 14159 (-2)
                          .empty
                          .empty)
                        (.node 14185 (-2)
                          .empty
                          .empty))
                      (.node 14269 (2)
                        (.node 14249 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 14512 (2)
                    (.node 14420 (2)
                      (.node 14363 (-2)
                        (.node 14323 (-2)
                          .empty
                          .empty)
                        (.node 14373 (2)
                          .empty
                          .empty))
                      (.node 14444 (-2)
                        (.node 14421 (-2)
                          .empty
                          .empty)
                        (.node 14445 (2)
                          .empty
                          .empty)))
                    (.node 14636 (-2)
                      (.node 14573 (-2)
                        (.node 14560 (2)
                          .empty
                          .empty)
                        (.node 14613 (-2)
                          .empty
                          .empty))
                      (.node 14706 (-2)
                        (.node 14684 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 16597 (2)
              (.node 15609 (-2)
                (.node 15157 (-2)
                  (.node 14914 (2)
                    (.node 14799 (-2)
                      (.node 14735 (-2)
                        (.node 14728 (2)
                          .empty
                          .empty)
                        (.node 14767 (2)
                          .empty
                          .empty))
                      (.node 14844 (2)
                        (.node 14829 (-2)
                          .empty
                          .empty)
                        (.node 14901 (-2)
                          .empty
                          .empty)))
                    (.node 14976 (-2)
                      (.node 14948 (-2)
                        (.node 14931 (-2)
                          .empty
                          .empty)
                        (.node 14961 (2)
                          .empty
                          .empty))
                      (.node 15084 (-2)
                        (.node 15082 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 15427 (2)
                    (.node 15306 (2)
                      (.node 15211 (-2)
                        (.node 15202 (2)
                          .empty
                          .empty)
                        (.node 15213 (2)
                          .empty
                          .empty))
                      (.node 15362 (2)
                        (.node 15310 (2)
                          .empty
                          .empty)
                        (.node 15363 (-2)
                          .empty
                          .empty)))
                    (.node 15543 (2)
                      (.node 15475 (2)
                        (.node 15428 (-2)
                          .empty
                          .empty)
                        (.node 15477 (-2)
                          .empty
                          .empty))
                      (.node 15608 (2)
                        (.node 15591 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 16131 (-2)
                  (.node 15940 (-2)
                    (.node 15842 (-2)
                      (.node 15773 (2)
                        (.node 15771 (-2)
                          .empty
                          .empty)
                        (.node 15834 (2)
                          .empty
                          .empty))
                      (.node 15853 (2)
                        (.node 15851 (-2)
                          .empty
                          .empty)
                        (.node 15930 (-2)
                          .empty
                          .empty)))
                    (.node 16013 (-2)
                      (.node 15975 (2)
                        (.node 15961 (-2)
                          .empty
                          .empty)
                        (.node 16011 (2)
                          .empty
                          .empty))
                      (.node 16098 (2)
                        (.node 16074 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 16400 (2)
                    (.node 16306 (2)
                      (.node 16245 (2)
                        (.node 16133 (2)
                          .empty
                          .empty)
                        (.node 16260 (-2)
                          .empty
                          .empty))
                      (.node 16362 (-2)
                        (.node 16338 (2)
                          .empty
                          .empty)
                        (.node 16365 (2)
                          .empty
                          .empty)))
                    (.node 16499 (2)
                      (.node 16458 (-2)
                        (.node 16407 (2)
                          .empty
                          .empty)
                        (.node 16460 (2)
                          .empty
                          .empty))
                      (.node 16590 (-2)
                        (.node 16501 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 17285 (-2)
                (.node 16992 (2)
                  (.node 16825 (2)
                    (.node 16736 (2)
                      (.node 16677 (2)
                        (.node 16671 (-2)
                          .empty
                          .empty)
                        (.node 16730 (-2)
                          .empty
                          .empty))
                      (.node 16801 (-2)
                        (.node 16795 (2)
                          .empty
                          .empty)
                        (.node 16810 (-2)
                          .empty
                          .empty)))
                    (.node 16881 (-2)
                      (.node 16864 (-2)
                        (.node 16851 (-2)
                          .empty
                          .empty)
                        (.node 16876 (-2)
                          .empty
                          .empty))
                      (.node 16919 (-2)
                        (.node 16906 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 17134 (-2)
                    (.node 17048 (-2)
                      (.node 17039 (2)
                        (.node 16993 (-2)
                          .empty
                          .empty)
                        (.node 17041 (2)
                          .empty
                          .empty))
                      (.node 17080 (-2)
                        (.node 17062 (2)
                          .empty
                          .empty)
                        (.node 17111 (2)
                          .empty
                          .empty)))
                    (.node 17209 (2)
                      (.node 17170 (-2)
                        (.node 17159 (2)
                          .empty
                          .empty)
                        (.node 17179 (-2)
                          .empty
                          .empty))
                      (.node 17284 (2)
                        (.node 17217 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 17709 (-2)
                  (.node 17527 (-2)
                    (.node 17401 (-2)
                      (.node 17377 (-2)
                        (.node 17334 (2)
                          .empty
                          .empty)
                        (.node 17400 (2)
                          .empty
                          .empty))
                      (.node 17510 (2)
                        (.node 17462 (2)
                          .empty
                          .empty)
                        (.node 17513 (2)
                          .empty
                          .empty)))
                    (.node 17623 (-2)
                      (.node 17536 (2)
                        (.node 17534 (2)
                          .empty
                          .empty)
                        (.node 17600 (2)
                          .empty
                          .empty))
                      (.node 17667 (2)
                        (.node 17651 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 17917 (-2)
                    (.node 17849 (-2)
                      (.node 17772 (-2)
                        (.node 17724 (2)
                          .empty
                          .empty)
                        (.node 17820 (-2)
                          .empty
                          .empty))
                      (.node 17896 (2)
                        (.node 17889 (-2)
                          .empty
                          .empty)
                        (.node 17910 (-2)
                          .empty
                          .empty)))
                    (.node 17992 (2)
                      (.node 17967 (-2)
                        (.node 17923 (-2)
                          .empty
                          .empty)
                        (.node 17977 (2)
                          .empty
                          .empty))
                      (.node 18033 (-2)
                        (.node 18014 (2)
                          .empty
                          .empty)
                        .empty)))))))
          (.node 21376 (2)
            (.node 19699 (-2)
              (.node 18940 (2)
                (.node 18439 (-2)
                  (.node 18276 (2)
                    (.node 18140 (2)
                      (.node 18118 (-2)
                        (.node 18113 (2)
                          .empty
                          .empty)
                        (.node 18139 (2)
                          .empty
                          .empty))
                      (.node 18208 (-2)
                        (.node 18160 (-2)
                          .empty
                          .empty)
                        (.node 18261 (-2)
                          .empty
                          .empty)))
                    (.node 18359 (-2)
                      (.node 18341 (2)
                        (.node 18321 (2)
                          .empty
                          .empty)
                        (.node 18345 (2)
                          .empty
                          .empty))
                      (.node 18403 (2)
                        (.node 18397 (2)
                          .empty
                          .empty)
                        (.node 18435 (-2)
                          .empty
                          .empty))))
                  (.node 18745 (2)
                    (.node 18605 (2)
                      (.node 18556 (-2)
                        (.node 18541 (2)
                          .empty
                          .empty)
                        (.node 18604 (-2)
                          .empty
                          .empty))
                      (.node 18709 (2)
                        (.node 18708 (-2)
                          .empty
                          .empty)
                        (.node 18744 (-2)
                          .empty
                          .empty)))
                    (.node 18909 (2)
                      (.node 18844 (-2)
                        (.node 18803 (2)
                          .empty
                          .empty)
                        (.node 18861 (2)
                          .empty
                          .empty))
                      (.node 18929 (2)
                        (.node 18927 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 19325 (-2)
                  (.node 19130 (2)
                    (.node 19053 (-2)
                      (.node 18995 (2)
                        (.node 18946 (2)
                          .empty
                          .empty)
                        (.node 19021 (-2)
                          .empty
                          .empty))
                      (.node 19092 (2)
                        (.node 19073 (2)
                          .empty
                          .empty)
                        (.node 19096 (2)
                          .empty
                          .empty)))
                    (.node 19245 (-2)
                      (.node 19218 (2)
                        (.node 19134 (2)
                          .empty
                          .empty)
                        (.node 19219 (-2)
                          .empty
                          .empty))
                      (.node 19315 (2)
                        (.node 19260 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 19524 (-2)
                    (.node 19410 (2)
                      (.node 19366 (2)
                        (.node 19336 (2)
                          .empty
                          .empty)
                        (.node 19371 (2)
                          .empty
                          .empty))
                      (.node 19494 (-2)
                        (.node 19447 (-2)
                          .empty
                          .empty)
                        (.node 19513 (2)
                          .empty
                          .empty)))
                    (.node 19612 (-2)
                      (.node 19555 (2)
                        (.node 19550 (2)
                          .empty
                          .empty)
                        (.node 19592 (-2)
                          .empty
                          .empty))
                      (.node 19644 (2)
                        (.node 19629 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 20568 (2)
                (.node 20056 (-2)
                  (.node 19924 (2)
                    (.node 19852 (2)
                      (.node 19819 (2)
                        (.node 19715 (2)
                          .empty
                          .empty)
                        (.node 19832 (-2)
                          .empty
                          .empty))
                      (.node 19885 (2)
                        (.node 19871 (2)
                          .empty
                          .empty)
                        (.node 19902 (-2)
                          .empty
                          .empty)))
                    (.node 20009 (2)
                      (.node 19959 (2)
                        (.node 19943 (2)
                          .empty
                          .empty)
                        (.node 19974 (-2)
                          .empty
                          .empty))
                      (.node 20052 (-2)
                        (.node 20037 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 20267 (2)
                    (.node 20155 (-2)
                      (.node 20133 (2)
                        (.node 20082 (-2)
                          .empty
                          .empty)
                        (.node 20137 (-2)
                          .empty
                          .empty))
                      (.node 20263 (-2)
                        (.node 20262 (2)
                          .empty
                          .empty)
                        (.node 20266 (-2)
                          .empty
                          .empty)))
                    (.node 20422 (2)
                      (.node 20361 (2)
                        (.node 20360 (-2)
                          .empty
                          .empty)
                        (.node 20407 (-2)
                          .empty
                          .empty))
                      (.node 20478 (-2)
                        (.node 20476 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 21030 (2)
                  (.node 20796 (-2)
                    (.node 20661 (2)
                      (.node 20587 (2)
                        (.node 20570 (2)
                          .empty
                          .empty)
                        (.node 20602 (-2)
                          .empty
                          .empty))
                      (.node 20721 (2)
                        (.node 20679 (2)
                          .empty
                          .empty)
                        (.node 20774 (-2)
                          .empty
                          .empty)))
                    (.node 20847 (2)
                      (.node 20814 (-2)
                        (.node 20807 (2)
                          .empty
                          .empty)
                        (.node 20821 (-2)
                          .empty
                          .empty))
                      (.node 21018 (2)
                        (.node 20895 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 21223 (-2)
                    (.node 21135 (2)
                      (.node 21081 (2)
                        (.node 21033 (2)
                          .empty
                          .empty)
                        (.node 21119 (-2)
                          .empty
                          .empty))
                      (.node 21184 (-2)
                        (.node 21174 (2)
                          .empty
                          .empty)
                        (.node 21201 (-2)
                          .empty
                          .empty)))
                    (.node 21313 (2)
                      (.node 21280 (-2)
                        (.node 21232 (-2)
                          .empty
                          .empty)
                        (.node 21308 (2)
                          .empty
                          .empty))
                      (.node 21332 (2)
                        (.node 21321 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 23189 (-2)
              (.node 22207 (2)
                (.node 21667 (-2)
                  (.node 21581 (-2)
                    (.node 21483 (2)
                      (.node 21444 (-2)
                        (.node 21395 (2)
                          .empty
                          .empty)
                        (.node 21446 (2)
                          .empty
                          .empty))
                      (.node 21517 (-2)
                        (.node 21496 (2)
                          .empty
                          .empty)
                        (.node 21534 (2)
                          .empty
                          .empty)))
                    (.node 21623 (-2)
                      (.node 21598 (-2)
                        (.node 21587 (-2)
                          .empty
                          .empty)
                        (.node 21600 (2)
                          .empty
                          .empty))
                      (.node 21646 (-2)
                        (.node 21626 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 21892 (-2)
                    (.node 21798 (2)
                      (.node 21734 (-2)
                        (.node 21719 (2)
                          .empty
                          .empty)
                        (.node 21737 (-2)
                          .empty
                          .empty))
                      (.node 21861 (-2)
                        (.node 21802 (2)
                          .empty
                          .empty)
                        (.node 21877 (2)
                          .empty
                          .empty)))
                    (.node 22024 (2)
                      (.node 21962 (-2)
                        (.node 21960 (2)
                          .empty
                          .empty)
                        (.node 22023 (-2)
                          .empty
                          .empty))
                      (.node 22110 (-2)
                        (.node 22067 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 22657 (-2)
                  (.node 22444 (2)
                    (.node 22317 (2)
                      (.node 22276 (2)
                        (.node 22227 (-2)
                          .empty
                          .empty)
                        (.node 22277 (-2)
                          .empty
                          .empty))
                      (.node 22382 (-2)
                        (.node 22332 (-2)
                          .empty
                          .empty)
                        (.node 22430 (-2)
                          .empty
                          .empty)))
                    (.node 22579 (2)
                      (.node 22509 (2)
                        (.node 22492 (2)
                          .empty
                          .empty)
                        (.node 22524 (-2)
                          .empty
                          .empty))
                      (.node 22649 (-2)
                        (.node 22622 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 22938 (2)
                    (.node 22774 (-2)
                      (.node 22758 (-2)
                        (.node 22754 (-2)
                          .empty
                          .empty)
                        (.node 22773 (2)
                          .empty
                          .empty))
                      (.node 22842 (-2)
                        (.node 22841 (2)
                          .empty
                          .empty)
                        (.node 22937 (-2)
                          .empty
                          .empty)))
                    (.node 23046 (2)
                      (.node 22974 (2)
                        (.node 22973 (-2)
                          .empty
                          .empty)
                        (.node 23045 (-2)
                          .empty
                          .empty))
                      (.node 23142 (-2)
                        (.node 23089 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 24112 (2)
                (.node 23658 (-2)
                  (.node 23441 (-2)
                    (.node 23273 (-2)
                      (.node 23217 (2)
                        (.node 23190 (2)
                          .empty
                          .empty)
                        (.node 23218 (-2)
                          .empty
                          .empty))
                      (.node 23362 (-2)
                        (.node 23274 (2)
                          .empty
                          .empty)
                        (.node 23373 (2)
                          .empty
                          .empty)))
                    (.node 23541 (-2)
                      (.node 23513 (2)
                        (.node 23442 (2)
                          .empty
                          .empty)
                        (.node 23514 (-2)
                          .empty
                          .empty))
                      (.node 23657 (2)
                        (.node 23577 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 23891 (-2)
                    (.node 23834 (-2)
                      (.node 23782 (-2)
                        (.node 23733 (-2)
                          .empty
                          .empty)
                        (.node 23785 (-2)
                          .empty
                          .empty))
                      (.node 23879 (2)
                        (.node 23865 (-2)
                          .empty
                          .empty)
                        (.node 23885 (-2)
                          .empty
                          .empty)))
                    (.node 24009 (-2)
                      (.node 23938 (2)
                        (.node 23937 (-2)
                          .empty
                          .empty)
                        (.node 23993 (2)
                          .empty
                          .empty))
                      (.node 24098 (-2)
                        (.node 24097 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 24337 (2)
                  (.node 24232 (2)
                    (.node 24169 (-2)
                      (.node 24150 (-2)
                        (.node 24131 (2)
                          .empty
                          .empty)
                        (.node 24165 (2)
                          .empty
                          .empty))
                      (.node 24212 (2)
                        (.node 24190 (-2)
                          .empty
                          .empty)
                        (.node 24227 (-2)
                          .empty
                          .empty)))
                    (.node 24301 (2)
                      (.node 24253 (2)
                        (.node 24243 (2)
                          .empty
                          .empty)
                        (.node 24262 (-2)
                          .empty
                          .empty))
                      (.node 24334 (-2)
                        (.node 24306 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 24517 (2)
                    (.node 24415 (-2)
                      (.node 24380 (-2)
                        (.node 24373 (-2)
                          .empty
                          .empty)
                        (.node 24406 (2)
                          .empty
                          .empty))
                      (.node 24462 (2)
                        (.node 24449 (-2)
                          .empty
                          .empty)
                        (.node 24494 (2)
                          .empty
                          .empty)))
                    (.node 24562 (2)
                      (.node 24550 (2)
                        (.node 24525 (-2)
                          .empty
                          .empty)
                        (.node 24561 (-2)
                          .empty
                          .empty))
                      (.node 24641 (2)
                        (.node 24636 (2)
                          .empty
                          .empty)
                        .empty)))))))))
      (.node 36461 (2)
        (.node 30245 (-2)
          (.node 27985 (-2)
            (.node 26299 (-2)
              (.node 25427 (2)
                (.node 25110 (2)
                  (.node 24946 (2)
                    (.node 24762 (-2)
                      (.node 24682 (2)
                        (.node 24678 (2)
                          .empty
                          .empty)
                        (.node 24730 (2)
                          .empty
                          .empty))
                      (.node 24809 (2)
                        (.node 24774 (-2)
                          .empty
                          .empty)
                        (.node 24821 (2)
                          .empty
                          .empty)))
                    (.node 25010 (-2)
                      (.node 24952 (2)
                        (.node 24949 (-2)
                          .empty
                          .empty)
                        (.node 24959 (2)
                          .empty
                          .empty))
                      (.node 25077 (2)
                        (.node 25058 (-2)
                          .empty
                          .empty)
                        (.node 25090 (2)
                          .empty
                          .empty))))
                  (.node 25268 (-2)
                    (.node 25201 (-2)
                      (.node 25153 (2)
                        (.node 25121 (-2)
                          .empty
                          .empty)
                        (.node 25154 (-2)
                          .empty
                          .empty))
                      (.node 25210 (2)
                        (.node 25206 (-2)
                          .empty
                          .empty)
                        (.node 25213 (-2)
                          .empty
                          .empty)))
                    (.node 25361 (2)
                      (.node 25320 (-2)
                        (.node 25316 (-2)
                          .empty
                          .empty)
                        (.node 25346 (-2)
                          .empty
                          .empty))
                      (.node 25393 (2)
                        (.node 25371 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 25877 (-2)
                  (.node 25635 (2)
                    (.node 25502 (-2)
                      (.node 25467 (-2)
                        (.node 25453 (-2)
                          .empty
                          .empty)
                        (.node 25480 (2)
                          .empty
                          .empty))
                      (.node 25553 (-2)
                        (.node 25541 (2)
                          .empty
                          .empty)
                        (.node 25595 (2)
                          .empty
                          .empty)))
                    (.node 25758 (2)
                      (.node 25692 (-2)
                        (.node 25644 (-2)
                          .empty
                          .empty)
                        (.node 25724 (2)
                          .empty
                          .empty))
                      (.node 25795 (2)
                        (.node 25779 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 26141 (2)
                    (.node 26068 (-2)
                      (.node 25949 (2)
                        (.node 25878 (2)
                          .empty
                          .empty)
                        (.node 25950 (-2)
                          .empty
                          .empty))
                      (.node 26091 (2)
                        (.node 26086 (-2)
                          .empty
                          .empty)
                        (.node 26100 (2)
                          .empty
                          .empty)))
                    (.node 26261 (2)
                      (.node 26195 (2)
                        (.node 26146 (-2)
                          .empty
                          .empty)
                        (.node 26215 (2)
                          .empty
                          .empty))
                      (.node 26297 (-2)
                        (.node 26263 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 27156 (-2)
                (.node 26793 (2)
                  (.node 26577 (2)
                    (.node 26458 (-2)
                      (.node 26399 (-2)
                        (.node 26352 (2)
                          .empty
                          .empty)
                        (.node 26440 (-2)
                          .empty
                          .empty))
                      (.node 26534 (2)
                        (.node 26533 (-2)
                          .empty
                          .empty)
                        (.node 26558 (-2)
                          .empty
                          .empty)))
                    (.node 26719 (-2)
                      (.node 26644 (-2)
                        (.node 26604 (-2)
                          .empty
                          .empty)
                        (.node 26671 (-2)
                          .empty
                          .empty))
                      (.node 26778 (2)
                        (.node 26777 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 27062 (2)
                    (.node 26954 (2)
                      (.node 26877 (-2)
                        (.node 26795 (-2)
                          .empty
                          .empty)
                        (.node 26879 (2)
                          .empty
                          .empty))
                      (.node 26987 (2)
                        (.node 26961 (2)
                          .empty
                          .empty)
                        (.node 27035 (2)
                          .empty
                          .empty)))
                    (.node 27118 (2)
                      (.node 27088 (-2)
                        (.node 27073 (-2)
                          .empty
                          .empty)
                        (.node 27111 (-2)
                          .empty
                          .empty))
                      (.node 27147 (-2)
                        (.node 27121 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 27642 (2)
                  (.node 27410 (2)
                    (.node 27239 (-2)
                      (.node 27193 (2)
                        (.node 27182 (-2)
                          .empty
                          .empty)
                        (.node 27216 (-2)
                          .empty
                          .empty))
                      (.node 27263 (-2)
                        (.node 27243 (-2)
                          .empty
                          .empty)
                        (.node 27391 (-2)
                          .empty
                          .empty)))
                    (.node 27547 (-2)
                      (.node 27466 (2)
                        (.node 27465 (-2)
                          .empty
                          .empty)
                        (.node 27510 (2)
                          .empty
                          .empty))
                      (.node 27610 (-2)
                        (.node 27575 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 27868 (2)
                    (.node 27813 (-2)
                      (.node 27701 (-2)
                        (.node 27671 (-2)
                          .empty
                          .empty)
                        (.node 27717 (2)
                          .empty
                          .empty))
                      (.node 27833 (2)
                        (.node 27814 (2)
                          .empty
                          .empty)
                        (.node 27847 (-2)
                          .empty
                          .empty)))
                    (.node 27914 (2)
                      (.node 27889 (-2)
                        (.node 27874 (2)
                          .empty
                          .empty)
                        (.node 27906 (2)
                          .empty
                          .empty))
                      (.node 27966 (2)
                        (.node 27929 (2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 29183 (2)
              (.node 28583 (2)
                (.node 28249 (-2)
                  (.node 28128 (2)
                    (.node 28069 (2)
                      (.node 28027 (-2)
                        (.node 28017 (2)
                          .empty
                          .empty)
                        (.node 28047 (2)
                          .empty
                          .empty))
                      (.node 28086 (-2)
                        (.node 28073 (-2)
                          .empty
                          .empty)
                        (.node 28127 (-2)
                          .empty
                          .empty)))
                    (.node 28192 (2)
                      (.node 28153 (2)
                        (.node 28148 (-2)
                          .empty
                          .empty)
                        (.node 28173 (2)
                          .empty
                          .empty))
                      (.node 28245 (2)
                        (.node 28238 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 28362 (-2)
                    (.node 28308 (-2)
                      (.node 28273 (2)
                        (.node 28258 (2)
                          .empty
                          .empty)
                        (.node 28285 (2)
                          .empty
                          .empty))
                      (.node 28337 (2)
                        (.node 28312 (2)
                          .empty
                          .empty)
                        (.node 28344 (2)
                          .empty
                          .empty)))
                    (.node 28473 (2)
                      (.node 28422 (-2)
                        (.node 28387 (2)
                          .empty
                          .empty)
                        (.node 28438 (2)
                          .empty
                          .empty))
                      (.node 28535 (2)
                        (.node 28485 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 28905 (2)
                  (.node 28726 (-2)
                    (.node 28673 (2)
                      (.node 28641 (-2)
                        (.node 28593 (-2)
                          .empty
                          .empty)
                        (.node 28658 (2)
                          .empty
                          .empty))
                      (.node 28698 (2)
                        (.node 28681 (-2)
                          .empty
                          .empty)
                        (.node 28714 (-2)
                          .empty
                          .empty)))
                    (.node 28849 (2)
                      (.node 28816 (2)
                        (.node 28803 (2)
                          .empty
                          .empty)
                        (.node 28842 (2)
                          .empty
                          .empty))
                      (.node 28868 (-2)
                        (.node 28863 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 29045 (2)
                    (.node 28969 (-2)
                      (.node 28926 (-2)
                        (.node 28914 (-2)
                          .empty
                          .empty)
                        (.node 28933 (-2)
                          .empty
                          .empty))
                      (.node 28988 (-2)
                        (.node 28983 (2)
                          .empty
                          .empty)
                        (.node 28994 (-2)
                          .empty
                          .empty)))
                    (.node 29151 (-2)
                      (.node 29099 (-2)
                        (.node 29093 (2)
                          .empty
                          .empty)
                        (.node 29110 (2)
                          .empty
                          .empty))
                      (.node 29171 (2)
                        (.node 29154 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 29685 (-2)
                (.node 29465 (-2)
                  (.node 29346 (-2)
                    (.node 29245 (2)
                      (.node 29210 (2)
                        (.node 29206 (-2)
                          .empty
                          .empty)
                        (.node 29233 (2)
                          .empty
                          .empty))
                      (.node 29275 (2)
                        (.node 29271 (-2)
                          .empty
                          .empty)
                        (.node 29301 (2)
                          .empty
                          .empty)))
                    (.node 29380 (2)
                      (.node 29367 (-2)
                        (.node 29354 (-2)
                          .empty
                          .empty)
                        (.node 29369 (-2)
                          .empty
                          .empty))
                      (.node 29424 (-2)
                        (.node 29421 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 29560 (2)
                    (.node 29524 (2)
                      (.node 29480 (-2)
                        (.node 29476 (-2)
                          .empty
                          .empty)
                        (.node 29502 (-2)
                          .empty
                          .empty))
                      (.node 29547 (-2)
                        (.node 29538 (-2)
                          .empty
                          .empty)
                        (.node 29557 (-2)
                          .empty
                          .empty)))
                    (.node 29661 (2)
                      (.node 29609 (2)
                        (.node 29574 (-2)
                          .empty
                          .empty)
                        (.node 29623 (-2)
                          .empty
                          .empty))
                      (.node 29681 (-2)
                        (.node 29667 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 29964 (2)
                  (.node 29843 (-2)
                    (.node 29780 (2)
                      (.node 29761 (2)
                        (.node 29756 (2)
                          .empty
                          .empty)
                        (.node 29769 (-2)
                          .empty
                          .empty))
                      (.node 29825 (-2)
                        (.node 29818 (-2)
                          .empty
                          .empty)
                        (.node 29832 (2)
                          .empty
                          .empty)))
                    (.node 29941 (-2)
                      (.node 29914 (-2)
                        (.node 29878 (2)
                          .empty
                          .empty)
                        (.node 29930 (2)
                          .empty
                          .empty))
                      (.node 29952 (2)
                        (.node 29951 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 30106 (-2)
                    (.node 30005 (-2)
                      (.node 29977 (-2)
                        (.node 29971 (-2)
                          .empty
                          .empty)
                        (.node 29990 (2)
                          .empty
                          .empty))
                      (.node 30031 (2)
                        (.node 30022 (-2)
                          .empty
                          .empty)
                        (.node 30044 (-2)
                          .empty
                          .empty)))
                    (.node 30195 (2)
                      (.node 30169 (2)
                        (.node 30117 (-2)
                          .empty
                          .empty)
                        (.node 30182 (2)
                          .empty
                          .empty))
                      (.node 30223 (-2)
                        (.node 30201 (-2)
                          .empty
                          .empty)
                        .empty)))))))
          (.node 32864 (2)
            (.node 31552 (2)
              (.node 30933 (-2)
                (.node 30630 (-2)
                  (.node 30426 (-2)
                    (.node 30290 (-2)
                      (.node 30278 (-2)
                        (.node 30264 (2)
                          .empty
                          .empty)
                        (.node 30284 (-2)
                          .empty
                          .empty))
                      (.node 30350 (-2)
                        (.node 30337 (2)
                          .empty
                          .empty)
                        (.node 30408 (-2)
                          .empty
                          .empty)))
                    (.node 30487 (-2)
                      (.node 30470 (2)
                        (.node 30465 (2)
                          .empty
                          .empty)
                        (.node 30480 (2)
                          .empty
                          .empty))
                      (.node 30546 (2)
                        (.node 30504 (-2)
                          .empty
                          .empty)
                        (.node 30580 (2)
                          .empty
                          .empty))))
                  (.node 30815 (2)
                    (.node 30676 (-2)
                      (.node 30642 (2)
                        (.node 30637 (-2)
                          .empty
                          .empty)
                        (.node 30667 (-2)
                          .empty
                          .empty))
                      (.node 30733 (2)
                        (.node 30704 (2)
                          .empty
                          .empty)
                        (.node 30767 (2)
                          .empty
                          .empty)))
                    (.node 30864 (-2)
                      (.node 30835 (-2)
                        (.node 30828 (2)
                          .empty
                          .empty)
                        (.node 30863 (-2)
                          .empty
                          .empty))
                      (.node 30911 (2)
                        (.node 30899 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 31259 (-2)
                  (.node 31053 (-2)
                    (.node 30999 (2)
                      (.node 30964 (-2)
                        (.node 30937 (-2)
                          .empty
                          .empty)
                        (.node 30975 (-2)
                          .empty
                          .empty))
                      (.node 31016 (2)
                        (.node 31004 (-2)
                          .empty
                          .empty)
                        (.node 31035 (-2)
                          .empty
                          .empty)))
                    (.node 31153 (2)
                      (.node 31120 (2)
                        (.node 31070 (-2)
                          .empty
                          .empty)
                        (.node 31140 (2)
                          .empty
                          .empty))
                      (.node 31243 (2)
                        (.node 31187 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 31419 (2)
                    (.node 31363 (-2)
                      (.node 31313 (-2)
                        (.node 31302 (2)
                          .empty
                          .empty)
                        (.node 31348 (2)
                          .empty
                          .empty))
                      (.node 31392 (2)
                        (.node 31383 (2)
                          .empty
                          .empty)
                        (.node 31405 (2)
                          .empty
                          .empty)))
                    (.node 31526 (2)
                      (.node 31448 (-2)
                        (.node 31438 (2)
                          .empty
                          .empty)
                        (.node 31492 (2)
                          .empty
                          .empty))
                      (.node 31532 (-2)
                        (.node 31531 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 32195 (-2)
                (.node 31838 (2)
                  (.node 31744 (2)
                    (.node 31646 (-2)
                      (.node 31608 (-2)
                        (.node 31559 (-2)
                          .empty
                          .empty)
                        (.node 31619 (2)
                          .empty
                          .empty))
                      (.node 31664 (2)
                        (.node 31653 (-2)
                          .empty
                          .empty)
                        (.node 31712 (2)
                          .empty
                          .empty)))
                    (.node 31799 (2)
                      (.node 31771 (2)
                        (.node 31751 (-2)
                          .empty
                          .empty)
                        (.node 31772 (2)
                          .empty
                          .empty))
                      (.node 31817 (2)
                        (.node 31808 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 32039 (-2)
                    (.node 31926 (-2)
                      (.node 31890 (-2)
                        (.node 31855 (2)
                          .empty
                          .empty)
                        (.node 31913 (2)
                          .empty
                          .empty))
                      (.node 31957 (-2)
                        (.node 31946 (-2)
                          .empty
                          .empty)
                        (.node 32018 (-2)
                          .empty
                          .empty)))
                    (.node 32143 (-2)
                      (.node 32102 (-2)
                        (.node 32091 (-2)
                          .empty
                          .empty)
                        (.node 32130 (2)
                          .empty
                          .empty))
                      (.node 32173 (-2)
                        (.node 32170 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 32518 (2)
                  (.node 32335 (-2)
                    (.node 32265 (-2)
                      (.node 32250 (2)
                        (.node 32196 (-2)
                          .empty
                          .empty)
                        (.node 32261 (2)
                          .empty
                          .empty))
                      (.node 32305 (2)
                        (.node 32278 (2)
                          .empty
                          .empty)
                        (.node 32315 (-2)
                          .empty
                          .empty)))
                    (.node 32431 (-2)
                      (.node 32361 (-2)
                        (.node 32357 (-2)
                          .empty
                          .empty)
                        (.node 32381 (-2)
                          .empty
                          .empty))
                      (.node 32516 (-2)
                        (.node 32480 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 32683 (2)
                    (.node 32662 (2)
                      (.node 32563 (-2)
                        (.node 32555 (-2)
                          .empty
                          .empty)
                        (.node 32649 (-2)
                          .empty
                          .empty))
                      (.node 32677 (2)
                        (.node 32666 (2)
                          .empty
                          .empty)
                        (.node 32681 (-2)
                          .empty
                          .empty)))
                    (.node 32807 (-2)
                      (.node 32763 (2)
                        (.node 32750 (-2)
                          .empty
                          .empty)
                        (.node 32786 (-2)
                          .empty
                          .empty))
                      (.node 32830 (2)
                        (.node 32825 (2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 34602 (-2)
              (.node 33728 (2)
                (.node 33174 (2)
                  (.node 32970 (-2)
                    (.node 32917 (-2)
                      (.node 32875 (-2)
                        (.node 32871 (-2)
                          .empty
                          .empty)
                        (.node 32896 (-2)
                          .empty
                          .empty))
                      (.node 32950 (-2)
                        (.node 32926 (2)
                          .empty
                          .empty)
                        (.node 32955 (-2)
                          .empty
                          .empty)))
                    (.node 33067 (-2)
                      (.node 33030 (2)
                        (.node 32999 (2)
                          .empty
                          .empty)
                        (.node 33033 (2)
                          .empty
                          .empty))
                      (.node 33144 (2)
                        (.node 33081 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 33469 (-2)
                    (.node 33296 (2)
                      (.node 33208 (-2)
                        (.node 33196 (2)
                          .empty
                          .empty)
                        (.node 33278 (2)
                          .empty
                          .empty))
                      (.node 33445 (-2)
                        (.node 33433 (-2)
                          .empty
                          .empty)
                        (.node 33455 (2)
                          .empty
                          .empty)))
                    (.node 33629 (-2)
                      (.node 33551 (2)
                        (.node 33519 (-2)
                          .empty
                          .empty)
                        (.node 33615 (2)
                          .empty
                          .empty))
                      (.node 33694 (2)
                        (.node 33648 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 34140 (-2)
                  (.node 33897 (2)
                    (.node 33841 (2)
                      (.node 33802 (-2)
                        (.node 33756 (2)
                          .empty
                          .empty)
                        (.node 33826 (-2)
                          .empty
                          .empty))
                      (.node 33876 (2)
                        (.node 33862 (2)
                          .empty
                          .empty)
                        (.node 33891 (-2)
                          .empty
                          .empty)))
                    (.node 34040 (2)
                      (.node 34021 (2)
                        (.node 33899 (-2)
                          .empty
                          .empty)
                        (.node 34023 (-2)
                          .empty
                          .empty))
                      (.node 34098 (-2)
                        (.node 34070 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 34297 (2)
                    (.node 34224 (-2)
                      (.node 34182 (-2)
                        (.node 34158 (-2)
                          .empty
                          .empty)
                        (.node 34223 (2)
                          .empty
                          .empty))
                      (.node 34261 (-2)
                        (.node 34250 (-2)
                          .empty
                          .empty)
                        (.node 34283 (-2)
                          .empty
                          .empty)))
                    (.node 34518 (2)
                      (.node 34463 (-2)
                        (.node 34448 (2)
                          .empty
                          .empty)
                        (.node 34488 (2)
                          .empty
                          .empty))
                      (.node 34582 (2)
                        (.node 34553 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 35584 (2)
                (.node 35079 (-2)
                  (.node 34801 (2)
                    (.node 34712 (-2)
                      (.node 34683 (2)
                        (.node 34645 (-2)
                          .empty
                          .empty)
                        (.node 34693 (-2)
                          .empty
                          .empty))
                      (.node 34758 (-2)
                        (.node 34726 (-2)
                          .empty
                          .empty)
                        (.node 34761 (-2)
                          .empty
                          .empty)))
                    (.node 34922 (-2)
                      (.node 34864 (-2)
                        (.node 34854 (-2)
                          .empty
                          .empty)
                        (.node 34910 (-2)
                          .empty
                          .empty))
                      (.node 35058 (2)
                        (.node 34980 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 35268 (2)
                    (.node 35151 (-2)
                      (.node 35105 (2)
                        (.node 35092 (2)
                          .empty
                          .empty)
                        (.node 35149 (2)
                          .empty
                          .empty))
                      (.node 35219 (2)
                        (.node 35217 (-2)
                          .empty
                          .empty)
                        (.node 35260 (2)
                          .empty
                          .empty)))
                    (.node 35386 (2)
                      (.node 35312 (-2)
                        (.node 35304 (-2)
                          .empty
                          .empty)
                        (.node 35384 (-2)
                          .empty
                          .empty))
                      (.node 35478 (2)
                        (.node 35476 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 36058 (-2)
                  (.node 35774 (-2)
                    (.node 35689 (2)
                      (.node 35634 (-2)
                        (.node 35598 (2)
                          .empty
                          .empty)
                        (.node 35685 (2)
                          .empty
                          .empty))
                      (.node 35728 (-2)
                        (.node 35694 (-2)
                          .empty
                          .empty)
                        (.node 35735 (-2)
                          .empty
                          .empty)))
                    (.node 35948 (2)
                      (.node 35847 (-2)
                        (.node 35792 (-2)
                          .empty
                          .empty)
                        (.node 35879 (2)
                          .empty
                          .empty))
                      (.node 36020 (-2)
                        (.node 36002 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 36283 (2)
                    (.node 36198 (2)
                      (.node 36132 (-2)
                        (.node 36074 (-2)
                          .empty
                          .empty)
                        (.node 36136 (2)
                          .empty
                          .empty))
                      (.node 36260 (-2)
                        (.node 36240 (-2)
                          .empty
                          .empty)
                        (.node 36264 (-2)
                          .empty
                          .empty)))
                    (.node 36386 (-2)
                      (.node 36318 (-2)
                        (.node 36301 (-2)
                          .empty
                          .empty)
                        (.node 36332 (-2)
                          .empty
                          .empty))
                      (.node 36450 (2)
                        (.node 36396 (2)
                          .empty
                          .empty)
                        .empty))))))))
        (.node 42691 (2)
          (.node 39740 (-2)
            (.node 38357 (2)
              (.node 37364 (-2)
                (.node 36849 (-2)
                  (.node 36652 (-2)
                    (.node 36560 (2)
                      (.node 36502 (-2)
                        (.node 36484 (-2)
                          .empty
                          .empty)
                        (.node 36511 (-2)
                          .empty
                          .empty))
                      (.node 36594 (2)
                        (.node 36575 (-2)
                          .empty
                          .empty)
                        (.node 36642 (2)
                          .empty
                          .empty)))
                    (.node 36797 (2)
                      (.node 36717 (-2)
                        (.node 36692 (-2)
                          .empty
                          .empty)
                        (.node 36765 (-2)
                          .empty
                          .empty))
                      (.node 36809 (-2)
                        (.node 36800 (-2)
                          .empty
                          .empty)
                        (.node 36820 (-2)
                          .empty
                          .empty))))
                  (.node 37188 (2)
                    (.node 37066 (-2)
                      (.node 37027 (-2)
                        (.node 36853 (-2)
                          .empty
                          .empty)
                        (.node 37029 (2)
                          .empty
                          .empty))
                      (.node 37123 (-2)
                        (.node 37068 (2)
                          .empty
                          .empty)
                        (.node 37140 (2)
                          .empty
                          .empty)))
                    (.node 37330 (2)
                      (.node 37252 (2)
                        (.node 37196 (2)
                          .empty
                          .empty)
                        (.node 37258 (2)
                          .empty
                          .empty))
                      (.node 37362 (2)
                        (.node 37332 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 37882 (2)
                  (.node 37687 (2)
                    (.node 37520 (2)
                      (.node 37466 (2)
                        (.node 37428 (2)
                          .empty
                          .empty)
                        (.node 37511 (-2)
                          .empty
                          .empty))
                      (.node 37640 (-2)
                        (.node 37608 (-2)
                          .empty
                          .empty)
                        (.node 37674 (-2)
                          .empty
                          .empty)))
                    (.node 37757 (2)
                      (.node 37696 (2)
                        (.node 37693 (2)
                          .empty
                          .empty)
                        (.node 37755 (-2)
                          .empty
                          .empty))
                      (.node 37860 (2)
                        (.node 37858 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 38165 (2)
                    (.node 38002 (-2)
                      (.node 37971 (-2)
                        (.node 37908 (2)
                          .empty
                          .empty)
                        (.node 37973 (2)
                          .empty
                          .empty))
                      (.node 38130 (-2)
                        (.node 38050 (-2)
                          .empty
                          .empty)
                        (.node 38143 (-2)
                          .empty
                          .empty)))
                    (.node 38282 (2)
                      (.node 38205 (-2)
                        (.node 38168 (-2)
                          .empty
                          .empty)
                        (.node 38218 (-2)
                          .empty
                          .empty))
                      (.node 38355 (-2)
                        (.node 38284 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 38998 (2)
                (.node 38706 (-2)
                  (.node 38580 (2)
                    (.node 38484 (2)
                      (.node 38434 (2)
                        (.node 38380 (2)
                          .empty
                          .empty)
                        (.node 38458 (2)
                          .empty
                          .empty))
                      (.node 38554 (2)
                        (.node 38549 (-2)
                          .empty
                          .empty)
                        (.node 38571 (-2)
                          .empty
                          .empty)))
                    (.node 38644 (2)
                      (.node 38631 (2)
                        (.node 38616 (2)
                          .empty
                          .empty)
                        (.node 38639 (2)
                          .empty
                          .empty))
                      (.node 38658 (-2)
                        (.node 38649 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 38856 (-2)
                    (.node 38768 (-2)
                      (.node 38732 (2)
                        (.node 38719 (-2)
                          .empty
                          .empty)
                        (.node 38753 (-2)
                          .empty
                          .empty))
                      (.node 38834 (-2)
                        (.node 38788 (-2)
                          .empty
                          .empty)
                        (.node 38843 (2)
                          .empty
                          .empty)))
                    (.node 38975 (-2)
                      (.node 38895 (-2)
                        (.node 38881 (-2)
                          .empty
                          .empty)
                        (.node 38943 (-2)
                          .empty
                          .empty))
                      (.node 38987 (2)
                        (.node 38978 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 39371 (-2)
                  (.node 39264 (-2)
                    (.node 39102 (-2)
                      (.node 39028 (-2)
                        (.node 39018 (2)
                          .empty
                          .empty)
                        (.node 39080 (2)
                          .empty
                          .empty))
                      (.node 39198 (2)
                        (.node 39184 (2)
                          .empty
                          .empty)
                        (.node 39214 (-2)
                          .empty
                          .empty)))
                    (.node 39330 (-2)
                      (.node 39297 (2)
                        (.node 39272 (-2)
                          .empty
                          .empty)
                        (.node 39307 (-2)
                          .empty
                          .empty))
                      (.node 39359 (2)
                        (.node 39346 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 39539 (2)
                    (.node 39478 (2)
                      (.node 39416 (2)
                        (.node 39398 (-2)
                          .empty
                          .empty)
                        (.node 39446 (2)
                          .empty
                          .empty))
                      (.node 39504 (-2)
                        (.node 39491 (2)
                          .empty
                          .empty)
                        (.node 39525 (2)
                          .empty
                          .empty)))
                    (.node 39656 (-2)
                      (.node 39610 (-2)
                        (.node 39588 (-2)
                          .empty
                          .empty)
                        (.node 39636 (-2)
                          .empty
                          .empty))
                      (.node 39723 (2)
                        (.node 39660 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 41057 (2)
              (.node 40356 (-2)
                (.node 39984 (-2)
                  (.node 39895 (2)
                    (.node 39804 (-2)
                      (.node 39783 (-2)
                        (.node 39760 (-2)
                          .empty
                          .empty)
                        (.node 39787 (-2)
                          .empty
                          .empty))
                      (.node 39847 (2)
                        (.node 39824 (-2)
                          .empty
                          .empty)
                        (.node 39881 (-2)
                          .empty
                          .empty)))
                    (.node 39935 (-2)
                      (.node 39908 (2)
                        (.node 39898 (2)
                          .empty
                          .empty)
                        (.node 39922 (-2)
                          .empty
                          .empty))
                      (.node 39960 (-2)
                        (.node 39957 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 40232 (-2)
                    (.node 40116 (-2)
                      (.node 40059 (-2)
                        (.node 40032 (-2)
                          .empty
                          .empty)
                        (.node 40076 (-2)
                          .empty
                          .empty))
                      (.node 40198 (-2)
                        (.node 40164 (-2)
                          .empty
                          .empty)
                        (.node 40208 (-2)
                          .empty
                          .empty)))
                    (.node 40296 (-2)
                      (.node 40275 (-2)
                        (.node 40255 (2)
                          .empty
                          .empty)
                        (.node 40292 (-2)
                          .empty
                          .empty))
                      (.node 40339 (-2)
                        (.node 40319 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 40744 (2)
                  (.node 40614 (-2)
                    (.node 40476 (-2)
                      (.node 40402 (-2)
                        (.node 40380 (-2)
                          .empty
                          .empty)
                        (.node 40434 (-2)
                          .empty
                          .empty))
                      (.node 40551 (2)
                        (.node 40519 (-2)
                          .empty
                          .empty)
                        (.node 40576 (2)
                          .empty
                          .empty)))
                    (.node 40695 (-2)
                      (.node 40679 (2)
                        (.node 40624 (-2)
                          .empty
                          .empty)
                        (.node 40688 (-2)
                          .empty
                          .empty))
                      (.node 40701 (-2)
                        (.node 40698 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 40887 (2)
                    (.node 40808 (2)
                      (.node 40783 (-2)
                        (.node 40771 (2)
                          .empty
                          .empty)
                        (.node 40804 (2)
                          .empty
                          .empty))
                      (.node 40851 (2)
                        (.node 40831 (-2)
                          .empty
                          .empty)
                        (.node 40868 (2)
                          .empty
                          .empty)))
                    (.node 40977 (2)
                      (.node 40948 (-2)
                        (.node 40919 (2)
                          .empty
                          .empty)
                        (.node 40952 (2)
                          .empty
                          .empty))
                      (.node 41009 (2)
                        (.node 40989 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 41892 (2)
                (.node 41388 (2)
                  (.node 41216 (-2)
                    (.node 41125 (-2)
                      (.node 41073 (-2)
                        (.node 41068 (2)
                          .empty
                          .empty)
                        (.node 41112 (-2)
                          .empty
                          .empty))
                      (.node 41182 (-2)
                        (.node 41136 (-2)
                          .empty
                          .empty)
                        (.node 41207 (2)
                          .empty
                          .empty)))
                    (.node 41308 (-2)
                      (.node 41243 (-2)
                        (.node 41228 (-2)
                          .empty
                          .empty)
                        (.node 41304 (-2)
                          .empty
                          .empty))
                      (.node 41374 (-2)
                        (.node 41328 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 41664 (2)
                    (.node 41528 (2)
                      (.node 41454 (2)
                        (.node 41443 (-2)
                          .empty
                          .empty)
                        (.node 41502 (2)
                          .empty
                          .empty))
                      (.node 41588 (-2)
                        (.node 41568 (2)
                          .empty
                          .empty)
                        (.node 41635 (2)
                          .empty
                          .empty)))
                    (.node 41838 (-2)
                      (.node 41768 (2)
                        (.node 41678 (2)
                          .empty
                          .empty)
                        (.node 41788 (2)
                          .empty
                          .empty))
                      (.node 41879 (2)
                        (.node 41853 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 42354 (-2)
                  (.node 42148 (2)
                    (.node 42011 (-2)
                      (.node 41928 (-2)
                        (.node 41926 (-2)
                          .empty
                          .empty)
                        (.node 41995 (2)
                          .empty
                          .empty))
                      (.node 42086 (2)
                        (.node 42024 (2)
                          .empty
                          .empty)
                        (.node 42090 (2)
                          .empty
                          .empty)))
                    (.node 42276 (2)
                      (.node 42214 (2)
                        (.node 42152 (2)
                          .empty
                          .empty)
                        (.node 42258 (-2)
                          .empty
                          .empty))
                      (.node 42342 (-2)
                        (.node 42328 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 42547 (-2)
                    (.node 42446 (-2)
                      (.node 42420 (2)
                        (.node 42396 (-2)
                          .empty
                          .empty)
                        (.node 42439 (2)
                          .empty
                          .empty))
                      (.node 42490 (-2)
                        (.node 42461 (2)
                          .empty
                          .empty)
                        (.node 42516 (-2)
                          .empty
                          .empty)))
                    (.node 42643 (2)
                      (.node 42614 (-2)
                        (.node 42595 (-2)
                          .empty
                          .empty)
                        (.node 42618 (2)
                          .empty
                          .empty))
                      (.node 42670 (-2)
                        (.node 42655 (2)
                          .empty
                          .empty)
                        .empty)))))))
          (.node 46078 (-2)
            (.node 44274 (-2)
              (.node 43467 (2)
                (.node 43144 (-2)
                  (.node 42918 (-2)
                    (.node 42770 (-2)
                      (.node 42714 (2)
                        (.node 42711 (2)
                          .empty
                          .empty)
                        (.node 42732 (-2)
                          .empty
                          .empty))
                      (.node 42835 (2)
                        (.node 42820 (-2)
                          .empty
                          .empty)
                        (.node 42857 (2)
                          .empty
                          .empty)))
                    (.node 42978 (-2)
                      (.node 42948 (-2)
                        (.node 42929 (-2)
                          .empty
                          .empty)
                        (.node 42967 (2)
                          .empty
                          .empty))
                      (.node 43036 (-2)
                        (.node 43016 (-2)
                          .empty
                          .empty)
                        (.node 43142 (-2)
                          .empty
                          .empty))))
                  (.node 43359 (-2)
                    (.node 43301 (-2)
                      (.node 43230 (-2)
                        (.node 43184 (-2)
                          .empty
                          .empty)
                        (.node 43297 (-2)
                          .empty
                          .empty))
                      (.node 43349 (-2)
                        (.node 43346 (-2)
                          .empty
                          .empty)
                        (.node 43352 (2)
                          .empty
                          .empty)))
                    (.node 43422 (-2)
                      (.node 43385 (-2)
                        (.node 43380 (-2)
                          .empty
                          .empty)
                        (.node 43411 (2)
                          .empty
                          .empty))
                      (.node 43447 (-2)
                        (.node 43432 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 43910 (-2)
                  (.node 43708 (2)
                    (.node 43579 (-2)
                      (.node 43504 (-2)
                        (.node 43476 (2)
                          .empty
                          .empty)
                        (.node 43551 (2)
                          .empty
                          .empty))
                      (.node 43624 (-2)
                        (.node 43604 (2)
                          .empty
                          .empty)
                        (.node 43658 (-2)
                          .empty
                          .empty)))
                    (.node 43838 (-2)
                      (.node 43760 (2)
                        (.node 43730 (2)
                          .empty
                          .empty)
                        (.node 43807 (-2)
                          .empty
                          .empty))
                      (.node 43889 (2)
                        (.node 43856 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 44033 (-2)
                    (.node 43970 (-2)
                      (.node 43936 (2)
                        (.node 43927 (2)
                          .empty
                          .empty)
                        (.node 43944 (-2)
                          .empty
                          .empty))
                      (.node 43998 (2)
                        (.node 43988 (-2)
                          .empty
                          .empty)
                        (.node 44026 (-2)
                          .empty
                          .empty)))
                    (.node 44118 (-2)
                      (.node 44068 (-2)
                        (.node 44063 (2)
                          .empty
                          .empty)
                        (.node 44084 (-2)
                          .empty
                          .empty))
                      (.node 44236 (-2)
                        (.node 44224 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 45242 (-2)
                (.node 44764 (2)
                  (.node 44524 (-2)
                    (.node 44414 (-2)
                      (.node 44328 (2)
                        (.node 44316 (-2)
                          .empty
                          .empty)
                        (.node 44346 (2)
                          .empty
                          .empty))
                      (.node 44468 (2)
                        (.node 44432 (-2)
                          .empty
                          .empty)
                        (.node 44486 (2)
                          .empty
                          .empty)))
                    (.node 44663 (-2)
                      (.node 44593 (-2)
                        (.node 44572 (-2)
                          .empty
                          .empty)
                        (.node 44641 (-2)
                          .empty
                          .empty))
                      (.node 44722 (2)
                        (.node 44704 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 45024 (2)
                    (.node 44887 (-2)
                      (.node 44830 (2)
                        (.node 44787 (-2)
                          .empty
                          .empty)
                        (.node 44858 (2)
                          .empty
                          .empty))
                      (.node 44966 (2)
                        (.node 44907 (-2)
                          .empty
                          .empty)
                        (.node 44974 (2)
                          .empty
                          .empty)))
                    (.node 45148 (-2)
                      (.node 45094 (-2)
                        (.node 45086 (-2)
                          .empty
                          .empty)
                        (.node 45106 (-2)
                          .empty
                          .empty))
                      (.node 45214 (-2)
                        (.node 45168 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 45687 (-2)
                  (.node 45551 (2)
                    (.node 45367 (-2)
                      (.node 45290 (2)
                        (.node 45268 (-2)
                          .empty
                          .empty)
                        (.node 45348 (2)
                          .empty
                          .empty))
                      (.node 45480 (2)
                        (.node 45402 (2)
                          .empty
                          .empty)
                        (.node 45528 (2)
                          .empty
                          .empty)))
                    (.node 45614 (2)
                      (.node 45586 (-2)
                        (.node 45574 (2)
                          .empty
                          .empty)
                        (.node 45595 (2)
                          .empty
                          .empty))
                      (.node 45675 (-2)
                        (.node 45662 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 45902 (-2)
                    (.node 45815 (2)
                      (.node 45790 (2)
                        (.node 45742 (2)
                          .empty
                          .empty)
                        (.node 45808 (-2)
                          .empty
                          .empty))
                      (.node 45821 (-2)
                        (.node 45818 (-2)
                          .empty
                          .empty)
                        (.node 45889 (2)
                          .empty
                          .empty)))
                    (.node 46017 (2)
                      (.node 45984 (-2)
                        (.node 45932 (-2)
                          .empty
                          .empty)
                        (.node 46002 (-2)
                          .empty
                          .empty))
                      (.node 46040 (-2)
                        (.node 46027 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 47478 (2)
              (.node 46798 (-2)
                (.node 46433 (-2)
                  (.node 46318 (2)
                    (.node 46202 (-2)
                      (.node 46138 (-2)
                        (.node 46084 (2)
                          .empty
                          .empty)
                        (.node 46158 (-2)
                          .empty
                          .empty))
                      (.node 46255 (2)
                        (.node 46208 (2)
                          .empty
                          .empty)
                        (.node 46261 (-2)
                          .empty
                          .empty)))
                    (.node 46391 (2)
                      (.node 46329 (2)
                        (.node 46320 (2)
                          .empty
                          .empty)
                        (.node 46343 (-2)
                          .empty
                          .empty))
                      (.node 46410 (2)
                        (.node 46396 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 46618 (2)
                    (.node 46524 (2)
                      (.node 46480 (-2)
                        (.node 46462 (-2)
                          .empty
                          .empty)
                        (.node 46511 (2)
                          .empty
                          .empty))
                      (.node 46566 (2)
                        (.node 46549 (-2)
                          .empty
                          .empty)
                        (.node 46580 (2)
                          .empty
                          .empty)))
                    (.node 46744 (2)
                      (.node 46646 (2)
                        (.node 46638 (2)
                          .empty
                          .empty)
                        (.node 46696 (2)
                          .empty
                          .empty))
                      (.node 46788 (2)
                        (.node 46760 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 47183 (-2)
                  (.node 46960 (-2)
                    (.node 46879 (-2)
                      (.node 46856 (2)
                        (.node 46818 (-2)
                          .empty
                          .empty)
                        (.node 46870 (-2)
                          .empty
                          .empty))
                      (.node 46895 (-2)
                        (.node 46881 (-2)
                          .empty
                          .empty)
                        (.node 46944 (2)
                          .empty
                          .empty)))
                    (.node 47094 (2)
                      (.node 47038 (2)
                        (.node 47015 (2)
                          .empty
                          .empty)
                        (.node 47056 (2)
                          .empty
                          .empty))
                      (.node 47181 (2)
                        (.node 47128 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 47346 (-2)
                    (.node 47319 (2)
                      (.node 47255 (-2)
                        (.node 47224 (2)
                          .empty
                          .empty)
                        (.node 47312 (2)
                          .empty
                          .empty))
                      (.node 47326 (2)
                        (.node 47321 (-2)
                          .empty
                          .empty)
                        (.node 47340 (-2)
                          .empty
                          .empty)))
                    (.node 47407 (2)
                      (.node 47398 (2)
                        (.node 47384 (-2)
                          .empty
                          .empty)
                        (.node 47400 (2)
                          .empty
                          .empty))
                      (.node 47454 (2)
                        (.node 47449 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 48385 (2)
                (.node 47871 (-2)
                  (.node 47678 (-2)
                    (.node 47616 (2)
                      (.node 47546 (-2)
                        (.node 47526 (2)
                          .empty
                          .empty)
                        (.node 47574 (-2)
                          .empty
                          .empty))
                      (.node 47641 (2)
                        (.node 47623 (2)
                          .empty
                          .empty)
                        (.node 47646 (-2)
                          .empty
                          .empty)))
                    (.node 47832 (-2)
                      (.node 47752 (-2)
                        (.node 47696 (-2)
                          .empty
                          .empty)
                        (.node 47754 (2)
                          .empty
                          .empty))
                      (.node 47869 (2)
                        (.node 47840 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 48097 (2)
                    (.node 47970 (2)
                      (.node 47940 (-2)
                        (.node 47921 (2)
                          .empty
                          .empty)
                        (.node 47959 (2)
                          .empty
                          .empty))
                      (.node 48026 (-2)
                        (.node 47988 (-2)
                          .empty
                          .empty)
                        (.node 48054 (-2)
                          .empty
                          .empty)))
                    (.node 48224 (-2)
                      (.node 48163 (2)
                        (.node 48159 (-2)
                          .empty
                          .empty)
                        (.node 48220 (2)
                          .empty
                          .empty))
                      (.node 48320 (-2)
                        (.node 48316 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 48864 (-2)
                  (.node 48568 (-2)
                    (.node 48498 (-2)
                      (.node 48424 (2)
                        (.node 48387 (-2)
                          .empty
                          .empty)
                        (.node 48486 (2)
                          .empty
                          .empty))
                      (.node 48524 (2)
                        (.node 48504 (2)
                          .empty
                          .empty)
                        (.node 48550 (2)
                          .empty
                          .empty)))
                    (.node 48705 (2)
                      (.node 48652 (-2)
                        (.node 48599 (2)
                          .empty
                          .empty)
                        (.node 48660 (-2)
                          .empty
                          .empty))
                      (.node 48814 (-2)
                        (.node 48707 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 49144 (2)
                    (.node 48994 (2)
                      (.node 48910 (2)
                        (.node 48896 (2)
                          .empty
                          .empty)
                        (.node 48949 (-2)
                          .empty
                          .empty))
                      (.node 49094 (2)
                        (.node 49092 (-2)
                          .empty
                          .empty)
                        (.node 49129 (-2)
                          .empty
                          .empty)))
                    (.node 49201 (-2)
                      (.node 49195 (-2)
                        (.node 49161 (2)
                          .empty
                          .empty)
                        (.node 49197 (2)
                          .empty
                          .empty))
                      (.node 49224 (2)
                        (.node 49216 (2)
                          .empty
                          .empty)
                        .empty))))))))))
    (.node 73647 (-2)
      (.node 60668 (2)
        (.node 54415 (-2)
          (.node 51768 (2)
            (.node 50445 (-2)
              (.node 49928 (-2)
                (.node 49524 (-2)
                  (.node 49391 (-2)
                    (.node 49296 (2)
                      (.node 49261 (2)
                        (.node 49258 (-2)
                          .empty
                          .empty)
                        (.node 49284 (2)
                          .empty
                          .empty))
                      (.node 49355 (-2)
                        (.node 49319 (-2)
                          .empty
                          .empty)
                        (.node 49368 (2)
                          .empty
                          .empty)))
                    (.node 49465 (-2)
                      (.node 49437 (2)
                        (.node 49435 (-2)
                          .empty
                          .empty)
                        (.node 49448 (-2)
                          .empty
                          .empty))
                      (.node 49507 (-2)
                        (.node 49480 (2)
                          .empty
                          .empty)
                        (.node 49509 (2)
                          .empty
                          .empty))))
                  (.node 49796 (-2)
                    (.node 49676 (-2)
                      (.node 49607 (2)
                        (.node 49584 (-2)
                          .empty
                          .empty)
                        (.node 49650 (-2)
                          .empty
                          .empty))
                      (.node 49746 (2)
                        (.node 49700 (-2)
                          .empty
                          .empty)
                        (.node 49772 (-2)
                          .empty
                          .empty)))
                    (.node 49871 (2)
                      (.node 49813 (-2)
                        (.node 49810 (2)
                          .empty
                          .empty)
                        (.node 49848 (-2)
                          .empty
                          .empty))
                      (.node 49919 (2)
                        (.node 49883 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 50188 (-2)
                  (.node 50077 (2)
                    (.node 50023 (-2)
                      (.node 49959 (-2)
                        (.node 49958 (2)
                          .empty
                          .empty)
                        (.node 49985 (2)
                          .empty
                          .empty))
                      (.node 50049 (2)
                        (.node 50038 (2)
                          .empty
                          .empty)
                        (.node 50074 (-2)
                          .empty
                          .empty)))
                    (.node 50151 (2)
                      (.node 50120 (2)
                        (.node 50099 (2)
                          .empty
                          .empty)
                        (.node 50150 (-2)
                          .empty
                          .empty))
                      (.node 50186 (2)
                        (.node 50180 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 50328 (2)
                    (.node 50266 (2)
                      (.node 50251 (-2)
                        (.node 50211 (-2)
                          .empty
                          .empty)
                        (.node 50253 (2)
                          .empty
                          .empty))
                      (.node 50294 (-2)
                        (.node 50269 (-2)
                          .empty
                          .empty)
                        (.node 50295 (2)
                          .empty
                          .empty)))
                    (.node 50414 (2)
                      (.node 50361 (2)
                        (.node 50351 (-2)
                          .empty
                          .empty)
                        (.node 50394 (-2)
                          .empty
                          .empty))
                      (.node 50443 (2)
                        (.node 50415 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 51262 (-2)
                (.node 50725 (2)
                  (.node 50576 (-2)
                    (.node 50512 (-2)
                      (.node 50471 (2)
                        (.node 50448 (-2)
                          .empty
                          .empty)
                        (.node 50484 (2)
                          .empty
                          .empty))
                      (.node 50550 (-2)
                        (.node 50542 (-2)
                          .empty
                          .empty)
                        (.node 50561 (2)
                          .empty
                          .empty)))
                    (.node 50662 (2)
                      (.node 50636 (2)
                        (.node 50604 (-2)
                          .empty
                          .empty)
                        (.node 50647 (-2)
                          .empty
                          .empty))
                      (.node 50722 (-2)
                        (.node 50700 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 51051 (2)
                    (.node 50885 (2)
                      (.node 50801 (-2)
                        (.node 50790 (2)
                          .empty
                          .empty)
                        (.node 50828 (-2)
                          .empty
                          .empty))
                      (.node 51019 (-2)
                        (.node 50985 (-2)
                          .empty
                          .empty)
                        (.node 51021 (2)
                          .empty
                          .empty)))
                    (.node 51210 (-2)
                      (.node 51161 (2)
                        (.node 51150 (-2)
                          .empty
                          .empty)
                        (.node 51188 (-2)
                          .empty
                          .empty))
                      (.node 51247 (2)
                        (.node 51234 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 51529 (2)
                  (.node 51426 (2)
                    (.node 51342 (2)
                      (.node 51293 (2)
                        (.node 51267 (-2)
                          .empty
                          .empty)
                        (.node 51317 (2)
                          .empty
                          .empty))
                      (.node 51366 (2)
                        (.node 51353 (-2)
                          .empty
                          .empty)
                        (.node 51377 (-2)
                          .empty
                          .empty)))
                    (.node 51494 (2)
                      (.node 51455 (2)
                        (.node 51432 (-4)
                          .empty
                          .empty)
                        (.node 51464 (2)
                          .empty
                          .empty))
                      (.node 51510 (2)
                        (.node 51495 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 51653 (-2)
                    (.node 51596 (2)
                      (.node 51552 (2)
                        (.node 51544 (-2)
                          .empty
                          .empty)
                        (.node 51575 (-2)
                          .empty
                          .empty))
                      (.node 51615 (2)
                        (.node 51614 (-2)
                          .empty
                          .empty)
                        (.node 51644 (-2)
                          .empty
                          .empty)))
                    (.node 51734 (-2)
                      (.node 51688 (2)
                        (.node 51673 (-2)
                          .empty
                          .empty)
                        (.node 51707 (-2)
                          .empty
                          .empty))
                      (.node 51764 (2)
                        (.node 51735 (2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 52949 (-2)
              (.node 52329 (-2)
                (.node 52048 (2)
                  (.node 51891 (-2)
                    (.node 51850 (2)
                      (.node 51817 (2)
                        (.node 51791 (-2)
                          .empty
                          .empty)
                        (.node 51832 (-2)
                          .empty
                          .empty))
                      (.node 51870 (2)
                        (.node 51853 (-2)
                          .empty
                          .empty)
                        (.node 51881 (-2)
                          .empty
                          .empty)))
                    (.node 52003 (-2)
                      (.node 51938 (2)
                        (.node 51917 (2)
                          .empty
                          .empty)
                        (.node 51940 (-2)
                          .empty
                          .empty))
                      (.node 52020 (-2)
                        (.node 52005 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 52199 (-2)
                    (.node 52122 (-2)
                      (.node 52086 (-2)
                        (.node 52063 (-2)
                          .empty
                          .empty)
                        (.node 52097 (2)
                          .empty
                          .empty))
                      (.node 52161 (2)
                        (.node 52133 (-2)
                          .empty
                          .empty)
                        (.node 52176 (2)
                          .empty
                          .empty)))
                    (.node 52270 (-2)
                      (.node 52235 (2)
                        (.node 52210 (2)
                          .empty
                          .empty)
                        (.node 52255 (2)
                          .empty
                          .empty))
                      (.node 52304 (2)
                        (.node 52287 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 52699 (2)
                  (.node 52598 (2)
                    (.node 52472 (2)
                      (.node 52410 (-2)
                        (.node 52386 (-2)
                          .empty
                          .empty)
                        (.node 52436 (-2)
                          .empty
                          .empty))
                      (.node 52547 (2)
                        (.node 52493 (2)
                          .empty
                          .empty)
                        (.node 52572 (-2)
                          .empty
                          .empty)))
                    (.node 52632 (-2)
                      (.node 52622 (2)
                        (.node 52599 (-2)
                          .empty
                          .empty)
                        (.node 52623 (-2)
                          .empty
                          .empty))
                      (.node 52667 (-2)
                        (.node 52655 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 52845 (-4)
                    (.node 52770 (-2)
                      (.node 52713 (2)
                        (.node 52701 (-2)
                          .empty
                          .empty)
                        (.node 52746 (-2)
                          .empty
                          .empty))
                      (.node 52804 (-2)
                        (.node 52794 (-2)
                          .empty
                          .empty)
                        (.node 52843 (2)
                          .empty
                          .empty)))
                    (.node 52895 (2)
                      (.node 52869 (-2)
                        (.node 52867 (2)
                          .empty
                          .empty)
                        (.node 52872 (-2)
                          .empty
                          .empty))
                      (.node 52935 (-2)
                        (.node 52934 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 53700 (-2)
                (.node 53312 (-2)
                  (.node 53114 (2)
                    (.node 53059 (-2)
                      (.node 53026 (2)
                        (.node 53000 (-2)
                          .empty
                          .empty)
                        (.node 53029 (-2)
                          .empty
                          .empty))
                      (.node 53084 (2)
                        (.node 53061 (2)
                          .empty
                          .empty)
                        (.node 53093 (-2)
                          .empty
                          .empty)))
                    (.node 53265 (-2)
                      (.node 53139 (-2)
                        (.node 53116 (-2)
                          .empty
                          .empty)
                        (.node 53202 (-2)
                          .empty
                          .empty))
                      (.node 53293 (-2)
                        (.node 53290 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 53521 (2)
                    (.node 53447 (2)
                      (.node 53360 (-2)
                        (.node 53339 (-2)
                          .empty
                          .empty)
                        (.node 53424 (-2)
                          .empty
                          .empty))
                      (.node 53491 (-2)
                        (.node 53459 (2)
                          .empty
                          .empty)
                        (.node 53493 (2)
                          .empty
                          .empty)))
                    (.node 53627 (2)
                      (.node 53580 (-2)
                        (.node 53536 (-2)
                          .empty
                          .empty)
                        (.node 53601 (-2)
                          .empty
                          .empty))
                      (.node 53673 (2)
                        (.node 53651 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 54121 (2)
                  (.node 53912 (-2)
                    (.node 53806 (-2)
                      (.node 53771 (-2)
                        (.node 53746 (-2)
                          .empty
                          .empty)
                        (.node 53791 (2)
                          .empty
                          .empty))
                      (.node 53850 (2)
                        (.node 53822 (2)
                          .empty
                          .empty)
                        (.node 53876 (-2)
                          .empty
                          .empty)))
                    (.node 54042 (-2)
                      (.node 53963 (2)
                        (.node 53940 (2)
                          .empty
                          .empty)
                        (.node 54005 (-2)
                          .empty
                          .empty))
                      (.node 54104 (2)
                        (.node 54081 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 54269 (2)
                    (.node 54212 (2)
                      (.node 54174 (2)
                        (.node 54136 (-2)
                          .empty
                          .empty)
                        (.node 54185 (-2)
                          .empty
                          .empty))
                      (.node 54239 (2)
                        (.node 54216 (-2)
                          .empty
                          .empty)
                        (.node 54251 (-2)
                          .empty
                          .empty)))
                    (.node 54381 (-2)
                      (.node 54330 (2)
                        (.node 54293 (2)
                          .empty
                          .empty)
                        (.node 54340 (2)
                          .empty
                          .empty))
                      (.node 54405 (-2)
                        (.node 54403 (2)
                          .empty
                          .empty)
                        .empty)))))))
          (.node 57432 (2)
            (.node 56000 (-2)
              (.node 55160 (-2)
                (.node 54744 (2)
                  (.node 54520 (-2)
                    (.node 54466 (-2)
                      (.node 54439 (-2)
                        (.node 54430 (2)
                          .empty
                          .empty)
                        (.node 54454 (2)
                          .empty
                          .empty))
                      (.node 54492 (-2)
                        (.node 54469 (2)
                          .empty
                          .empty)
                        (.node 54505 (2)
                          .empty
                          .empty)))
                    (.node 54612 (-2)
                      (.node 54571 (-2)
                        (.node 54539 (2)
                          .empty
                          .empty)
                        (.node 54573 (2)
                          .empty
                          .empty))
                      (.node 54680 (2)
                        (.node 54633 (2)
                          .empty
                          .empty)
                        (.node 54729 (2)
                          .empty
                          .empty))))
                  (.node 55055 (-2)
                    (.node 54876 (-2)
                      (.node 54800 (-2)
                        (.node 54767 (-2)
                          .empty
                          .empty)
                        (.node 54849 (-2)
                          .empty
                          .empty))
                      (.node 54996 (2)
                        (.node 54908 (2)
                          .empty
                          .empty)
                        (.node 55032 (2)
                          .empty
                          .empty)))
                    (.node 55103 (-2)
                      (.node 55077 (2)
                        (.node 55075 (-2)
                          .empty
                          .empty)
                        (.node 55080 (2)
                          .empty
                          .empty))
                      (.node 55140 (2)
                        (.node 55113 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 55612 (-2)
                  (.node 55423 (-2)
                    (.node 55255 (-2)
                      (.node 55205 (-2)
                        (.node 55194 (2)
                          .empty
                          .empty)
                        (.node 55244 (2)
                          .empty
                          .empty))
                      (.node 55325 (2)
                        (.node 55270 (2)
                          .empty
                          .empty)
                        (.node 55395 (2)
                          .empty
                          .empty)))
                    (.node 55529 (2)
                      (.node 55508 (2)
                        (.node 55438 (2)
                          .empty
                          .empty)
                        (.node 55518 (-2)
                          .empty
                          .empty))
                      (.node 55610 (2)
                        (.node 55602 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 55828 (2)
                    (.node 55715 (2)
                      (.node 55677 (2)
                        (.node 55675 (-2)
                          .empty
                          .empty)
                        (.node 55692 (2)
                          .empty
                          .empty))
                      (.node 55772 (2)
                        (.node 55736 (-2)
                          .empty
                          .empty)
                        (.node 55826 (-2)
                          .empty
                          .empty)))
                    (.node 55954 (2)
                      (.node 55889 (2)
                        (.node 55878 (-2)
                          .empty
                          .empty)
                        (.node 55923 (2)
                          .empty
                          .empty))
                      (.node 55977 (2)
                        (.node 55957 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 56524 (-2)
                (.node 56299 (-2)
                  (.node 56128 (2)
                    (.node 56078 (2)
                      (.node 56054 (-2)
                        (.node 56027 (2)
                          .empty
                          .empty)
                        (.node 56055 (2)
                          .empty
                          .empty))
                      (.node 56096 (2)
                        (.node 56079 (-2)
                          .empty
                          .empty)
                        (.node 56113 (-2)
                          .empty
                          .empty)))
                    (.node 56201 (2)
                      (.node 56171 (2)
                        (.node 56136 (2)
                          .empty
                          .empty)
                        (.node 56190 (-2)
                          .empty
                          .empty))
                      (.node 56259 (2)
                        (.node 56225 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 56418 (2)
                    (.node 56340 (2)
                      (.node 56323 (2)
                        (.node 56301 (2)
                          .empty
                          .empty)
                        (.node 56325 (-2)
                          .empty
                          .empty))
                      (.node 56378 (-2)
                        (.node 56364 (-2)
                          .empty
                          .empty)
                        (.node 56380 (2)
                          .empty
                          .empty)))
                    (.node 56496 (2)
                      (.node 56482 (2)
                        (.node 56442 (-2)
                          .empty
                          .empty)
                        (.node 56485 (-2)
                          .empty
                          .empty))
                      (.node 56522 (2)
                        (.node 56519 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 56799 (-2)
                  (.node 56667 (2)
                    (.node 56581 (-2)
                      (.node 56561 (2)
                        (.node 56550 (-2)
                          .empty
                          .empty)
                        (.node 56578 (2)
                          .empty
                          .empty))
                      (.node 56625 (2)
                        (.node 56603 (2)
                          .empty
                          .empty)
                        (.node 56648 (-2)
                          .empty
                          .empty)))
                    (.node 56737 (2)
                      (.node 56703 (-2)
                        (.node 56702 (2)
                          .empty
                          .empty)
                        (.node 56721 (2)
                          .empty
                          .empty))
                      (.node 56798 (2)
                        (.node 56782 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 57129 (2)
                    (.node 56880 (2)
                      (.node 56831 (-2)
                        (.node 56808 (2)
                          .empty
                          .empty)
                        (.node 56865 (-2)
                          .empty
                          .empty))
                      (.node 56946 (-2)
                        (.node 56903 (-2)
                          .empty
                          .empty)
                        (.node 57042 (2)
                          .empty
                          .empty)))
                    (.node 57252 (2)
                      (.node 57208 (-2)
                        (.node 57193 (2)
                          .empty
                          .empty)
                        (.node 57227 (2)
                          .empty
                          .empty))
                      (.node 57296 (-2)
                        (.node 57273 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 58905 (2)
              (.node 58194 (-2)
                (.node 57750 (2)
                  (.node 57586 (-2)
                    (.node 57501 (-2)
                      (.node 57464 (-2)
                        (.node 57455 (-2)
                          .empty
                          .empty)
                        (.node 57499 (2)
                          .empty
                          .empty))
                      (.node 57539 (2)
                        (.node 57516 (-2)
                          .empty
                          .empty)
                        (.node 57560 (-2)
                          .empty
                          .empty)))
                    (.node 57707 (-2)
                      (.node 57642 (2)
                        (.node 57589 (2)
                          .empty
                          .empty)
                        (.node 57672 (-2)
                          .empty
                          .empty))
                      (.node 57737 (2)
                        (.node 57726 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 57965 (2)
                    (.node 57839 (-2)
                      (.node 57812 (-2)
                        (.node 57761 (-4)
                          .empty
                          .empty)
                        (.node 57816 (2)
                          .empty
                          .empty))
                      (.node 57906 (2)
                        (.node 57882 (-2)
                          .empty
                          .empty)
                        (.node 57948 (-2)
                          .empty
                          .empty)))
                    (.node 58103 (2)
                      (.node 58053 (-2)
                        (.node 58051 (2)
                          .empty
                          .empty)
                        (.node 58080 (-2)
                          .empty
                          .empty))
                      (.node 58172 (2)
                        (.node 58148 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 58556 (2)
                  (.node 58376 (2)
                    (.node 58303 (-2)
                      (.node 58257 (-2)
                        (.node 58211 (2)
                          .empty
                          .empty)
                        (.node 58273 (-2)
                          .empty
                          .empty))
                      (.node 58335 (-2)
                        (.node 58334 (2)
                          .empty
                          .empty)
                        (.node 58356 (2)
                          .empty
                          .empty)))
                    (.node 58450 (2)
                      (.node 58396 (2)
                        (.node 58394 (-2)
                          .empty
                          .empty)
                        (.node 58421 (-2)
                          .empty
                          .empty))
                      (.node 58526 (-2)
                        (.node 58472 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 58764 (-2)
                    (.node 58659 (-2)
                      (.node 58617 (-2)
                        (.node 58595 (2)
                          .empty
                          .empty)
                        (.node 58652 (2)
                          .empty
                          .empty))
                      (.node 58747 (2)
                        (.node 58713 (-2)
                          .empty
                          .empty)
                        (.node 58749 (-2)
                          .empty
                          .empty)))
                    (.node 58828 (2)
                      (.node 58818 (2)
                        (.node 58779 (2)
                          .empty
                          .empty)
                        (.node 58826 (-2)
                          .empty
                          .empty))
                      (.node 58885 (-2)
                        (.node 58882 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 59850 (2)
                (.node 59435 (2)
                  (.node 59192 (2)
                    (.node 59044 (-2)
                      (.node 59019 (2)
                        (.node 58995 (-2)
                          .empty
                          .empty)
                        (.node 59042 (4)
                          .empty
                          .empty))
                      (.node 59124 (-2)
                        (.node 59085 (-2)
                          .empty
                          .empty)
                        (.node 59148 (2)
                          .empty
                          .empty)))
                    (.node 59307 (2)
                      (.node 59282 (2)
                        (.node 59237 (2)
                          .empty
                          .empty)
                        (.node 59284 (-2)
                          .empty
                          .empty))
                      (.node 59396 (2)
                        (.node 59372 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 59668 (2)
                    (.node 59574 (-2)
                      (.node 59546 (2)
                        (.node 59501 (-2)
                          .empty
                          .empty)
                        (.node 59548 (-2)
                          .empty
                          .empty))
                      (.node 59595 (-2)
                        (.node 59585 (2)
                          .empty
                          .empty)
                        (.node 59666 (-2)
                          .empty
                          .empty)))
                    (.node 59762 (-2)
                      (.node 59717 (2)
                        (.node 59691 (-2)
                          .empty
                          .empty)
                        (.node 59756 (-2)
                          .empty
                          .empty))
                      (.node 59811 (2)
                        (.node 59764 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 60243 (2)
                  (.node 60075 (-2)
                    (.node 59964 (-2)
                      (.node 59885 (2)
                        (.node 59876 (2)
                          .empty
                          .empty)
                        (.node 59922 (2)
                          .empty
                          .empty))
                      (.node 60008 (-2)
                        (.node 59986 (-2)
                          .empty
                          .empty)
                        (.node 60063 (-2)
                          .empty
                          .empty)))
                    (.node 60201 (2)
                      (.node 60155 (2)
                        (.node 60129 (-2)
                          .empty
                          .empty)
                        (.node 60179 (-2)
                          .empty
                          .empty))
                      (.node 60233 (-2)
                        (.node 60222 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 60471 (-2)
                    (.node 60332 (-2)
                      (.node 60287 (2)
                        (.node 60264 (-2)
                          .empty
                          .empty)
                        (.node 60296 (2)
                          .empty
                          .empty))
                      (.node 60435 (-2)
                        (.node 60341 (-2)
                          .empty
                          .empty)
                        (.node 60470 (2)
                          .empty
                          .empty)))
                    (.node 60555 (-2)
                      (.node 60520 (2)
                        (.node 60505 (-2)
                          .empty
                          .empty)
                        (.node 60539 (-2)
                          .empty
                          .empty))
                      (.node 60619 (-2)
                        (.node 60580 (-2)
                          .empty
                          .empty)
                        .empty))))))))
        (.node 67183 (-2)
          (.node 63732 (-2)
            (.node 62162 (-2)
              (.node 61532 (2)
                (.node 61035 (-2)
                  (.node 60823 (-2)
                    (.node 60723 (-2)
                      (.node 60703 (2)
                        (.node 60692 (-2)
                          .empty
                          .empty)
                        (.node 60718 (-2)
                          .empty
                          .empty))
                      (.node 60799 (2)
                        (.node 60788 (-2)
                          .empty
                          .empty)
                        (.node 60814 (-2)
                          .empty
                          .empty)))
                    (.node 60930 (2)
                      (.node 60845 (2)
                        (.node 60838 (2)
                          .empty
                          .empty)
                        (.node 60906 (-2)
                          .empty
                          .empty))
                      (.node 60986 (2)
                        (.node 60965 (-2)
                          .empty
                          .empty)
                        (.node 60988 (-2)
                          .empty
                          .empty))))
                  (.node 61371 (-2)
                    (.node 61232 (2)
                      (.node 61097 (2)
                        (.node 61086 (-2)
                          .empty
                          .empty)
                        (.node 61140 (2)
                          .empty
                          .empty))
                      (.node 61284 (2)
                        (.node 61257 (-2)
                          .empty
                          .empty)
                        (.node 61362 (-2)
                          .empty
                          .empty)))
                    (.node 61478 (-2)
                      (.node 61434 (-2)
                        (.node 61397 (-2)
                          .empty
                          .empty)
                        (.node 61452 (2)
                          .empty
                          .empty))
                      (.node 61496 (2)
                        (.node 61479 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 61910 (-2)
                  (.node 61786 (-2)
                    (.node 61676 (2)
                      (.node 61593 (-2)
                        (.node 61563 (-2)
                          .empty
                          .empty)
                        (.node 61611 (-2)
                          .empty
                          .empty))
                      (.node 61719 (2)
                        (.node 61691 (2)
                          .empty
                          .empty)
                        (.node 61770 (-2)
                          .empty
                          .empty)))
                    (.node 61864 (2)
                      (.node 61812 (2)
                        (.node 61789 (4)
                          .empty
                          .empty)
                        (.node 61849 (-2)
                          .empty
                          .empty))
                      (.node 61894 (2)
                        (.node 61879 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 62065 (2)
                    (.node 61979 (2)
                      (.node 61941 (2)
                        (.node 61911 (2)
                          .empty
                          .empty)
                        (.node 61946 (2)
                          .empty
                          .empty))
                      (.node 62028 (-2)
                        (.node 62012 (-2)
                          .empty
                          .empty)
                        (.node 62043 (2)
                          .empty
                          .empty)))
                    (.node 62127 (-2)
                      (.node 62097 (-2)
                        (.node 62080 (-2)
                          .empty
                          .empty)
                        (.node 62126 (2)
                          .empty
                          .empty))
                      (.node 62159 (-2)
                        (.node 62136 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 62850 (-2)
                (.node 62496 (2)
                  (.node 62317 (2)
                    (.node 62238 (2)
                      (.node 62195 (-2)
                        (.node 62164 (2)
                          .empty
                          .empty)
                        (.node 62211 (2)
                          .empty
                          .empty))
                      (.node 62265 (-2)
                        (.node 62249 (-2)
                          .empty
                          .empty)
                        (.node 62314 (-2)
                          .empty
                          .empty)))
                    (.node 62456 (2)
                      (.node 62388 (-2)
                        (.node 62336 (2)
                          .empty
                          .empty)
                        (.node 62442 (-2)
                          .empty
                          .empty))
                      (.node 62494 (2)
                        (.node 62479 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 62676 (2)
                    (.node 62581 (-2)
                      (.node 62529 (-2)
                        (.node 62519 (-2)
                          .empty
                          .empty)
                        (.node 62578 (2)
                          .empty
                          .empty))
                      (.node 62634 (2)
                        (.node 62595 (-2)
                          .empty
                          .empty)
                        (.node 62649 (-2)
                          .empty
                          .empty)))
                    (.node 62757 (-2)
                      (.node 62730 (-2)
                        (.node 62691 (-2)
                          .empty
                          .empty)
                        (.node 62755 (2)
                          .empty
                          .empty))
                      (.node 62829 (-2)
                        (.node 62827 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 63322 (-2)
                  (.node 63105 (2)
                    (.node 63036 (-2)
                      (.node 62957 (2)
                        (.node 62946 (2)
                          .empty
                          .empty)
                        (.node 62984 (-2)
                          .empty
                          .empty))
                      (.node 63078 (-2)
                        (.node 63059 (-2)
                          .empty
                          .empty)
                        (.node 63089 (2)
                          .empty
                          .empty)))
                    (.node 63219 (2)
                      (.node 63155 (-2)
                        (.node 63123 (2)
                          .empty
                          .empty)
                        (.node 63201 (2)
                          .empty
                          .empty))
                      (.node 63306 (2)
                        (.node 63254 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 63515 (-2)
                    (.node 63446 (-2)
                      (.node 63408 (-2)
                        (.node 63341 (2)
                          .empty
                          .empty)
                        (.node 63431 (2)
                          .empty
                          .empty))
                      (.node 63475 (2)
                        (.node 63447 (2)
                          .empty
                          .empty)
                        (.node 63482 (-2)
                          .empty
                          .empty)))
                    (.node 63627 (2)
                      (.node 63560 (2)
                        (.node 63531 (2)
                          .empty
                          .empty)
                        (.node 63596 (-2)
                          .empty
                          .empty))
                      (.node 63689 (2)
                        (.node 63678 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 65542 (2)
              (.node 64581 (-2)
                (.node 64209 (-2)
                  (.node 64012 (-2)
                    (.node 63932 (2)
                      (.node 63800 (-2)
                        (.node 63749 (2)
                          .empty
                          .empty)
                        (.node 63884 (-2)
                          .empty
                          .empty))
                      (.node 63987 (-2)
                        (.node 63971 (2)
                          .empty
                          .empty)
                        (.node 64010 (2)
                          .empty
                          .empty)))
                    (.node 64136 (2)
                      (.node 64110 (2)
                        (.node 64068 (2)
                          .empty
                          .empty)
                        (.node 64121 (-2)
                          .empty
                          .empty))
                      (.node 64181 (2)
                        (.node 64163 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 64402 (-2)
                    (.node 64285 (2)
                      (.node 64251 (2)
                        (.node 64242 (2)
                          .empty
                          .empty)
                        (.node 64282 (-2)
                          .empty
                          .empty))
                      (.node 64343 (2)
                        (.node 64320 (-2)
                          .empty
                          .empty)
                        (.node 64388 (-2)
                          .empty
                          .empty)))
                    (.node 64509 (-2)
                      (.node 64473 (-2)
                        (.node 64405 (2)
                          .empty
                          .empty)
                        (.node 64507 (2)
                          .empty
                          .empty))
                      (.node 64579 (2)
                        (.node 64539 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 65260 (-2)
                  (.node 65003 (-2)
                    (.node 64881 (-2)
                      (.node 64712 (2)
                        (.node 64635 (2)
                          .empty
                          .empty)
                        (.node 64832 (2)
                          .empty
                          .empty))
                      (.node 64942 (-2)
                        (.node 64927 (2)
                          .empty
                          .empty)
                        (.node 64986 (-2)
                          .empty
                          .empty)))
                    (.node 65130 (-2)
                      (.node 65076 (2)
                        (.node 65028 (2)
                          .empty
                          .empty)
                        (.node 65108 (-2)
                          .empty
                          .empty))
                      (.node 65258 (2)
                        (.node 65237 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 65380 (2)
                    (.node 65338 (-2)
                      (.node 65296 (-2)
                        (.node 65281 (2)
                          .empty
                          .empty)
                        (.node 65309 (-2)
                          .empty
                          .empty))
                      (.node 65360 (2)
                        (.node 65341 (2)
                          .empty
                          .empty)
                        (.node 65378 (-2)
                          .empty
                          .empty)))
                    (.node 65496 (2)
                      (.node 65429 (2)
                        (.node 65412 (2)
                          .empty
                          .empty)
                        (.node 65492 (-2)
                          .empty
                          .empty))
                      (.node 65527 (-2)
                        (.node 65519 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 66413 (2)
                (.node 65939 (2)
                  (.node 65669 (2)
                    (.node 65595 (2)
                      (.node 65587 (2)
                        (.node 65550 (-2)
                          .empty
                          .empty)
                        (.node 65589 (-2)
                          .empty
                          .empty))
                      (.node 65640 (2)
                        (.node 65616 (-2)
                          .empty
                          .empty)
                        (.node 65663 (-2)
                          .empty
                          .empty)))
                    (.node 65800 (-2)
                      (.node 65730 (2)
                        (.node 65697 (-2)
                          .empty
                          .empty)
                        (.node 65782 (-2)
                          .empty
                          .empty))
                      (.node 65924 (-2)
                        (.node 65828 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 66180 (-2)
                    (.node 66004 (2)
                      (.node 65967 (-2)
                        (.node 65966 (2)
                          .empty
                          .empty)
                        (.node 66002 (-2)
                          .empty
                          .empty))
                      (.node 66154 (-2)
                        (.node 66077 (2)
                          .empty
                          .empty)
                        (.node 66157 (2)
                          .empty
                          .empty)))
                    (.node 66336 (-2)
                      (.node 66271 (2)
                        (.node 66243 (-2)
                          .empty
                          .empty)
                        (.node 66286 (-2)
                          .empty
                          .empty))
                      (.node 66371 (-2)
                        (.node 66359 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 66779 (-2)
                  (.node 66611 (2)
                    (.node 66502 (-2)
                      (.node 66472 (-2)
                        (.node 66457 (2)
                          .empty
                          .empty)
                        (.node 66487 (2)
                          .empty
                          .empty))
                      (.node 66536 (2)
                        (.node 66507 (2)
                          .empty
                          .empty)
                        (.node 66561 (-2)
                          .empty
                          .empty)))
                    (.node 66685 (-2)
                      (.node 66668 (-2)
                        (.node 66642 (-2)
                          .empty
                          .empty)
                        (.node 66682 (2)
                          .empty
                          .empty))
                      (.node 66709 (2)
                        (.node 66706 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 67039 (-2)
                    (.node 66893 (-2)
                      (.node 66807 (-2)
                        (.node 66806 (2)
                          .empty
                          .empty)
                        (.node 66858 (2)
                          .empty
                          .empty))
                      (.node 66968 (-2)
                        (.node 66954 (-2)
                          .empty
                          .empty)
                        (.node 67017 (-2)
                          .empty
                          .empty)))
                    (.node 67125 (-2)
                      (.node 67097 (-2)
                        (.node 67054 (2)
                          .empty
                          .empty)
                        (.node 67123 (2)
                          .empty
                          .empty))
                      (.node 67152 (2)
                        (.node 67131 (-2)
                          .empty
                          .empty)
                        .empty)))))))
          (.node 70164 (2)
            (.node 68636 (-2)
              (.node 67961 (-2)
                (.node 67628 (2)
                  (.node 67364 (2)
                    (.node 67256 (2)
                      (.node 67212 (2)
                        (.node 67198 (2)
                          .empty
                          .empty)
                        (.node 67244 (-2)
                          .empty
                          .empty))
                      (.node 67318 (-4)
                        (.node 67303 (2)
                          .empty
                          .empty)
                        (.node 67336 (2)
                          .empty
                          .empty)))
                    (.node 67429 (2)
                      (.node 67384 (2)
                        (.node 67369 (-2)
                          .empty
                          .empty)
                        (.node 67426 (-2)
                          .empty
                          .empty))
                      (.node 67484 (-2)
                        (.node 67443 (2)
                          .empty
                          .empty)
                        (.node 67578 (2)
                          .empty
                          .empty))))
                  (.node 67767 (4)
                    (.node 67718 (-2)
                      (.node 67659 (2)
                        (.node 67640 (-2)
                          .empty
                          .empty)
                        (.node 67692 (-2)
                          .empty
                          .empty))
                      (.node 67739 (-2)
                        (.node 67719 (2)
                          .empty
                          .empty)
                        (.node 67766 (-2)
                          .empty
                          .empty)))
                    (.node 67914 (2)
                      (.node 67834 (-2)
                        (.node 67803 (2)
                          .empty
                          .empty)
                        (.node 67868 (2)
                          .empty
                          .empty))
                      (.node 67950 (2)
                        (.node 67929 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 68223 (2)
                  (.node 68101 (2)
                    (.node 68051 (-2)
                      (.node 67994 (2)
                        (.node 67987 (-2)
                          .empty
                          .empty)
                        (.node 68024 (2)
                          .empty
                          .empty))
                      (.node 68086 (-2)
                        (.node 68071 (2)
                          .empty
                          .empty)
                        (.node 68098 (-2)
                          .empty
                          .empty)))
                    (.node 68194 (-2)
                      (.node 68127 (2)
                        (.node 68126 (-2)
                          .empty
                          .empty)
                        (.node 68147 (-2)
                          .empty
                          .empty))
                      (.node 68222 (-2)
                        (.node 68197 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 68460 (-2)
                    (.node 68305 (-2)
                      (.node 68265 (-2)
                        (.node 68252 (-2)
                          .empty
                          .empty)
                        (.node 68298 (2)
                          .empty
                          .empty))
                      (.node 68379 (2)
                        (.node 68320 (2)
                          .empty
                          .empty)
                        (.node 68444 (-2)
                          .empty
                          .empty)))
                    (.node 68571 (-2)
                      (.node 68488 (2)
                        (.node 68473 (-2)
                          .empty
                          .empty)
                        (.node 68499 (-2)
                          .empty
                          .empty))
                      (.node 68608 (2)
                        (.node 68593 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 69393 (2)
                (.node 68987 (-2)
                  (.node 68791 (2)
                    (.node 68691 (2)
                      (.node 68653 (2)
                        (.node 68650 (-2)
                          .empty
                          .empty)
                        (.node 68672 (-2)
                          .empty
                          .empty))
                      (.node 68748 (-2)
                        (.node 68730 (-2)
                          .empty
                          .empty)
                        (.node 68769 (-2)
                          .empty
                          .empty)))
                    (.node 68900 (2)
                      (.node 68840 (2)
                        (.node 68806 (-2)
                          .empty
                          .empty)
                        (.node 68867 (-2)
                          .empty
                          .empty))
                      (.node 68920 (-2)
                        (.node 68905 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 69173 (2)
                    (.node 69028 (-2)
                      (.node 69013 (2)
                        (.node 69010 (-2)
                          .empty
                          .empty)
                        (.node 69026 (2)
                          .empty
                          .empty))
                      (.node 69108 (-2)
                        (.node 69081 (-2)
                          .empty
                          .empty)
                        (.node 69155 (-2)
                          .empty
                          .empty)))
                    (.node 69303 (2)
                      (.node 69224 (2)
                        (.node 69212 (-2)
                          .empty
                          .empty)
                        (.node 69273 (2)
                          .empty
                          .empty))
                      (.node 69370 (2)
                        (.node 69339 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 69760 (2)
                  (.node 69530 (-2)
                    (.node 69476 (-2)
                      (.node 69412 (-2)
                        (.node 69410 (2)
                          .empty
                          .empty)
                        (.node 69440 (2)
                          .empty
                          .empty))
                      (.node 69497 (-2)
                        (.node 69486 (2)
                          .empty
                          .empty)
                        (.node 69525 (-2)
                          .empty
                          .empty)))
                    (.node 69639 (-2)
                      (.node 69579 (-2)
                        (.node 69560 (-2)
                          .empty
                          .empty)
                        (.node 69638 (2)
                          .empty
                          .empty))
                      (.node 69745 (-2)
                        (.node 69692 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 69995 (-2)
                    (.node 69889 (2)
                      (.node 69803 (2)
                        (.node 69771 (2)
                          .empty
                          .empty)
                        (.node 69821 (-2)
                          .empty
                          .empty))
                      (.node 69924 (-2)
                        (.node 69904 (-2)
                          .empty
                          .empty)
                        (.node 69978 (-2)
                          .empty
                          .empty)))
                    (.node 70075 (2)
                      (.node 70029 (2)
                        (.node 70027 (-2)
                          .empty
                          .empty)
                        (.node 70037 (-2)
                          .empty
                          .empty))
                      (.node 70122 (2)
                        (.node 70077 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 71922 (-2)
              (.node 71132 (-2)
                (.node 70657 (2)
                  (.node 70371 (-2)
                    (.node 70232 (-2)
                      (.node 70193 (-2)
                        (.node 70182 (2)
                          .empty
                          .empty)
                        (.node 70203 (2)
                          .empty
                          .empty))
                      (.node 70281 (2)
                        (.node 70251 (2)
                          .empty
                          .empty)
                        (.node 70308 (2)
                          .empty
                          .empty)))
                    (.node 70566 (-2)
                      (.node 70428 (-2)
                        (.node 70410 (2)
                          .empty
                          .empty)
                        (.node 70517 (2)
                          .empty
                          .empty))
                      (.node 70616 (-2)
                        (.node 70577 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 70970 (2)
                    (.node 70765 (-2)
                      (.node 70688 (-2)
                        (.node 70672 (-2)
                          .empty
                          .empty)
                        (.node 70762 (2)
                          .empty
                          .empty))
                      (.node 70877 (-2)
                        (.node 70788 (2)
                          .empty
                          .empty)
                        (.node 70962 (-2)
                          .empty
                          .empty)))
                    (.node 71067 (-2)
                      (.node 71028 (-2)
                        (.node 70972 (-2)
                          .empty
                          .empty)
                        (.node 71045 (2)
                          .empty
                          .empty))
                      (.node 71111 (-2)
                        (.node 71088 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 71475 (-2)
                  (.node 71307 (-2)
                    (.node 71188 (-2)
                      (.node 71176 (-2)
                        (.node 71161 (2)
                          .empty
                          .empty)
                        (.node 71186 (2)
                          .empty
                          .empty))
                      (.node 71224 (-2)
                        (.node 71209 (2)
                          .empty
                          .empty)
                        (.node 71289 (2)
                          .empty
                          .empty)))
                    (.node 71438 (2)
                      (.node 71364 (-2)
                        (.node 71339 (-2)
                          .empty
                          .empty)
                        (.node 71409 (-2)
                          .empty
                          .empty))
                      (.node 71456 (2)
                        (.node 71439 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 71687 (2)
                    (.node 71587 (-2)
                      (.node 71536 (2)
                        (.node 71521 (-2)
                          .empty
                          .empty)
                        (.node 71549 (-2)
                          .empty
                          .empty))
                      (.node 71598 (-2)
                        (.node 71589 (2)
                          .empty
                          .empty)
                        (.node 71658 (2)
                          .empty
                          .empty)))
                    (.node 71830 (2)
                      (.node 71803 (-2)
                        (.node 71730 (2)
                          .empty
                          .empty)
                        (.node 71805 (2)
                          .empty
                          .empty))
                      (.node 71861 (2)
                        (.node 71833 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 72989 (-2)
                (.node 72448 (2)
                  (.node 72164 (2)
                    (.node 72062 (-2)
                      (.node 71972 (2)
                        (.node 71939 (2)
                          .empty
                          .empty)
                        (.node 71985 (-2)
                          .empty
                          .empty))
                      (.node 72098 (-2)
                        (.node 72063 (2)
                          .empty
                          .empty)
                        (.node 72100 (2)
                          .empty
                          .empty)))
                    (.node 72376 (2)
                      (.node 72323 (2)
                        (.node 72236 (2)
                          .empty
                          .empty)
                        (.node 72361 (-2)
                          .empty
                          .empty))
                      (.node 72433 (-2)
                        (.node 72428 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 72834 (-2)
                    (.node 72618 (2)
                      (.node 72561 (2)
                        (.node 72491 (2)
                          .empty
                          .empty)
                        (.node 72596 (-2)
                          .empty
                          .empty))
                      (.node 72703 (2)
                        (.node 72660 (2)
                          .empty
                          .empty)
                        (.node 72718 (-2)
                          .empty
                          .empty)))
                    (.node 72939 (2)
                      (.node 72876 (-2)
                        (.node 72845 (-2)
                          .empty
                          .empty)
                        (.node 72899 (-2)
                          .empty
                          .empty))
                      (.node 72976 (-2)
                        (.node 72961 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 73384 (4)
                  (.node 73256 (2)
                    (.node 73194 (-2)
                      (.node 73098 (2)
                        (.node 73017 (2)
                          .empty
                          .empty)
                        (.node 73145 (-2)
                          .empty
                          .empty))
                      (.node 73231 (-2)
                        (.node 73223 (-2)
                          .empty
                          .empty)
                        (.node 73246 (2)
                          .empty
                          .empty)))
                    (.node 73341 (2)
                      (.node 73287 (2)
                        (.node 73286 (-2)
                          .empty
                          .empty)
                        (.node 73339 (-2)
                          .empty
                          .empty))
                      (.node 73369 (-2)
                        (.node 73351 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 73574 (-2)
                    (.node 73448 (-2)
                      (.node 73430 (-2)
                        (.node 73397 (-2)
                          .empty
                          .empty)
                        (.node 73431 (2)
                          .empty
                          .empty))
                      (.node 73497 (2)
                        (.node 73467 (2)
                          .empty
                          .empty)
                        (.node 73515 (2)
                          .empty
                          .empty)))
                    (.node 73609 (-2)
                      (.node 73585 (2)
                        (.node 73575 (2)
                          .empty
                          .empty)
                        (.node 73600 (-2)
                          .empty
                          .empty))
                      (.node 73646 (2)
                        (.node 73624 (2)
                          .empty
                          .empty)
                        .empty)))))))))
      (.node 85324 (-2)
        (.node 79370 (-2)
          (.node 76604 (-2)
            (.node 75035 (2)
              (.node 74429 (2)
                (.node 74099 (-2)
                  (.node 73773 (2)
                    (.node 73723 (-2)
                      (.node 73677 (2)
                        (.node 73675 (-2)
                          .empty
                          .empty)
                        (.node 73683 (-2)
                          .empty
                          .empty))
                      (.node 73739 (2)
                        (.node 73725 (2)
                          .empty
                          .empty)
                        (.node 73771 (-2)
                          .empty
                          .empty)))
                    (.node 73923 (2)
                      (.node 73835 (-2)
                        (.node 73809 (-2)
                          .empty
                          .empty)
                        (.node 73883 (-2)
                          .empty
                          .empty))
                      (.node 74060 (2)
                        (.node 74012 (2)
                          .empty
                          .empty)
                        (.node 74067 (-2)
                          .empty
                          .empty))))
                  (.node 74280 (2)
                    (.node 74214 (-2)
                      (.node 74176 (-2)
                        (.node 74161 (2)
                          .empty
                          .empty)
                        (.node 74189 (-2)
                          .empty
                          .empty))
                      (.node 74262 (-2)
                        (.node 74225 (2)
                          .empty
                          .empty)
                        (.node 74273 (2)
                          .empty
                          .empty)))
                    (.node 74360 (-2)
                      (.node 74312 (-2)
                        (.node 74303 (-2)
                          .empty
                          .empty)
                        (.node 74339 (2)
                          .empty
                          .empty))
                      (.node 74420 (2)
                        (.node 74381 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 74744 (-2)
                  (.node 74573 (2)
                    (.node 74508 (2)
                      (.node 74465 (-2)
                        (.node 74454 (2)
                          .empty
                          .empty)
                        (.node 74485 (-2)
                          .empty
                          .empty))
                      (.node 74535 (-2)
                        (.node 74534 (2)
                          .empty
                          .empty)
                        (.node 74558 (2)
                          .empty
                          .empty)))
                    (.node 74706 (-2)
                      (.node 74652 (2)
                        (.node 74597 (2)
                          .empty
                          .empty)
                        (.node 74682 (-2)
                          .empty
                          .empty))
                      (.node 74728 (-2)
                        (.node 74713 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 74904 (2)
                    (.node 74826 (2)
                      (.node 74785 (-2)
                        (.node 74768 (2)
                          .empty
                          .empty)
                        (.node 74800 (2)
                          .empty
                          .empty))
                      (.node 74894 (2)
                        (.node 74850 (2)
                          .empty
                          .empty)
                        (.node 74895 (-2)
                          .empty
                          .empty)))
                    (.node 74967 (-2)
                      (.node 74940 (-2)
                        (.node 74927 (-2)
                          .empty
                          .empty)
                        (.node 74966 (2)
                          .empty
                          .empty))
                      (.node 75012 (-2)
                        (.node 74979 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 75921 (-2)
                (.node 75378 (2)
                  (.node 75225 (2)
                    (.node 75146 (-2)
                      (.node 75076 (2)
                        (.node 75068 (2)
                          .empty
                          .empty)
                        (.node 75115 (-2)
                          .empty
                          .empty))
                      (.node 75193 (-2)
                        (.node 75148 (2)
                          .empty
                          .empty)
                        (.node 75208 (2)
                          .empty
                          .empty)))
                    (.node 75313 (2)
                      (.node 75298 (2)
                        (.node 75272 (-2)
                          .empty
                          .empty)
                        (.node 75301 (-2)
                          .empty
                          .empty))
                      (.node 75341 (2)
                        (.node 75328 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 75629 (2)
                    (.node 75496 (-2)
                      (.node 75468 (-2)
                        (.node 75426 (2)
                          .empty
                          .empty)
                        (.node 75481 (2)
                          .empty
                          .empty))
                      (.node 75594 (2)
                        (.node 75546 (2)
                          .empty
                          .empty)
                        (.node 75605 (-2)
                          .empty
                          .empty)))
                    (.node 75851 (2)
                      (.node 75746 (-2)
                        (.node 75723 (-2)
                          .empty
                          .empty)
                        (.node 75748 (2)
                          .empty
                          .empty))
                      (.node 75899 (2)
                        (.node 75872 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 76181 (2)
                  (.node 76071 (-2)
                    (.node 75997 (-2)
                      (.node 75969 (-2)
                        (.node 75948 (-2)
                          .empty
                          .empty)
                        (.node 75994 (2)
                          .empty
                          .empty))
                      (.node 76044 (-2)
                        (.node 76021 (2)
                          .empty
                          .empty)
                        (.node 76070 (2)
                          .empty
                          .empty)))
                    (.node 76140 (2)
                      (.node 76095 (-2)
                        (.node 76094 (4)
                          .empty
                          .empty)
                        (.node 76116 (2)
                          .empty
                          .empty))
                      (.node 76167 (2)
                        (.node 76166 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 76373 (-2)
                    (.node 76263 (2)
                      (.node 76236 (2)
                        (.node 76212 (2)
                          .empty
                          .empty)
                        (.node 76262 (-2)
                          .empty
                          .empty))
                      (.node 76308 (-2)
                        (.node 76277 (2)
                          .empty
                          .empty)
                        (.node 76349 (-2)
                          .empty
                          .empty)))
                    (.node 76532 (2)
                      (.node 76457 (2)
                        (.node 76446 (-2)
                          .empty
                          .empty)
                        (.node 76482 (2)
                          .empty
                          .empty))
                      (.node 76569 (-2)
                        (.node 76544 (2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 78104 (-2)
              (.node 77451 (-2)
                (.node 77074 (2)
                  (.node 76854 (2)
                    (.node 76776 (-2)
                      (.node 76653 (-2)
                        (.node 76612 (-2)
                          .empty
                          .empty)
                        (.node 76772 (2)
                          .empty
                          .empty))
                      (.node 76831 (-2)
                        (.node 76809 (-2)
                          .empty
                          .empty)
                        (.node 76846 (2)
                          .empty
                          .empty)))
                    (.node 76979 (2)
                      (.node 76885 (2)
                        (.node 76882 (-2)
                          .empty
                          .empty)
                        (.node 76925 (2)
                          .empty
                          .empty))
                      (.node 77060 (-2)
                        (.node 77001 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 77231 (2)
                    (.node 77127 (-2)
                      (.node 77096 (2)
                        (.node 77077 (-2)
                          .empty
                          .empty)
                        (.node 77126 (2)
                          .empty
                          .empty))
                      (.node 77140 (-2)
                        (.node 77138 (2)
                          .empty
                          .empty)
                        (.node 77208 (-2)
                          .empty
                          .empty)))
                    (.node 77377 (4)
                      (.node 77267 (-2)
                        (.node 77240 (2)
                          .empty
                          .empty)
                        (.node 77363 (-2)
                          .empty
                          .empty))
                      (.node 77422 (-2)
                        (.node 77392 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 77800 (2)
                  (.node 77671 (2)
                    (.node 77602 (-2)
                      (.node 77507 (2)
                        (.node 77490 (2)
                          .empty
                          .empty)
                        (.node 77580 (-2)
                          .empty
                          .empty))
                      (.node 77647 (2)
                        (.node 77605 (2)
                          .empty
                          .empty)
                        (.node 77662 (-2)
                          .empty
                          .empty)))
                    (.node 77734 (-2)
                      (.node 77691 (-2)
                        (.node 77686 (-2)
                          .empty
                          .empty)
                        (.node 77719 (2)
                          .empty
                          .empty))
                      (.node 77785 (-2)
                        (.node 77768 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 77937 (-2)
                    (.node 77886 (2)
                      (.node 77849 (-2)
                        (.node 77838 (2)
                          .empty
                          .empty)
                        (.node 77876 (-2)
                          .empty
                          .empty))
                      (.node 77910 (2)
                        (.node 77897 (-2)
                          .empty
                          .empty)
                        (.node 77921 (-2)
                          .empty
                          .empty)))
                    (.node 78045 (2)
                      (.node 78016 (2)
                        (.node 78001 (-2)
                          .empty
                          .empty)
                        (.node 78043 (-2)
                          .empty
                          .empty))
                      (.node 78081 (2)
                        (.node 78056 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 78733 (-2)
                (.node 78401 (2)
                  (.node 78271 (-2)
                    (.node 78171 (2)
                      (.node 78142 (-2)
                        (.node 78127 (2)
                          .empty
                          .empty)
                        (.node 78149 (2)
                          .empty
                          .empty))
                      (.node 78223 (-2)
                        (.node 78197 (2)
                          .empty
                          .empty)
                        (.node 78238 (2)
                          .empty
                          .empty)))
                    (.node 78345 (2)
                      (.node 78293 (-2)
                        (.node 78286 (2)
                          .empty
                          .empty)
                        (.node 78312 (2)
                          .empty
                          .empty))
                      (.node 78382 (2)
                        (.node 78367 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 78524 (-2)
                    (.node 78436 (2)
                      (.node 78423 (2)
                        (.node 78422 (-2)
                          .empty
                          .empty)
                        (.node 78434 (-2)
                          .empty
                          .empty))
                      (.node 78481 (2)
                        (.node 78468 (2)
                          .empty
                          .empty)
                        (.node 78496 (-2)
                          .empty
                          .empty)))
                    (.node 78686 (2)
                      (.node 78587 (2)
                        (.node 78531 (-2)
                          .empty
                          .empty)
                        (.node 78636 (-2)
                          .empty
                          .empty))
                      (.node 78730 (2)
                        (.node 78687 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 79058 (2)
                  (.node 78879 (2)
                    (.node 78801 (2)
                      (.node 78761 (2)
                        (.node 78750 (-2)
                          .empty
                          .empty)
                        (.node 78773 (-2)
                          .empty
                          .empty))
                      (.node 78829 (2)
                        (.node 78826 (-2)
                          .empty
                          .empty)
                        (.node 78878 (-2)
                          .empty
                          .empty)))
                    (.node 78995 (-2)
                      (.node 78928 (-2)
                        (.node 78899 (2)
                          .empty
                          .empty)
                        (.node 78943 (-2)
                          .empty
                          .empty))
                      (.node 79035 (2)
                        (.node 79016 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 79173 (2)
                    (.node 79113 (2)
                      (.node 79099 (-2)
                        (.node 79060 (-2)
                          .empty
                          .empty)
                        (.node 79101 (2)
                          .empty
                          .empty))
                      (.node 79149 (2)
                        (.node 79147 (-2)
                          .empty
                          .empty)
                        (.node 79171 (-2)
                          .empty
                          .empty)))
                    (.node 79249 (-2)
                      (.node 79192 (2)
                        (.node 79177 (-2)
                          .empty
                          .empty)
                        (.node 79232 (2)
                          .empty
                          .empty))
                      (.node 79316 (-2)
                        (.node 79264 (2)
                          .empty
                          .empty)
                        .empty)))))))
          (.node 82397 (-2)
            (.node 80883 (2)
              (.node 80121 (2)
                (.node 79833 (2)
                  (.node 79593 (-2)
                    (.node 79444 (-2)
                      (.node 79410 (-2)
                        (.node 79372 (2)
                          .empty
                          .empty)
                        (.node 79442 (2)
                          .empty
                          .empty))
                      (.node 79561 (2)
                        (.node 79482 (2)
                          .empty
                          .empty)
                        (.node 79576 (-2)
                          .empty
                          .empty)))
                    (.node 79722 (-2)
                      (.node 79641 (-2)
                        (.node 79616 (2)
                          .empty
                          .empty)
                        (.node 79700 (-2)
                          .empty
                          .empty))
                      (.node 79801 (-2)
                        (.node 79748 (-2)
                          .empty
                          .empty)
                        (.node 79816 (2)
                          .empty
                          .empty))))
                  (.node 79988 (-2)
                    (.node 79913 (-2)
                      (.node 79875 (2)
                        (.node 79853 (2)
                          .empty
                          .empty)
                        (.node 79902 (2)
                          .empty
                          .empty))
                      (.node 79946 (2)
                        (.node 79938 (2)
                          .empty
                          .empty)
                        (.node 79948 (-2)
                          .empty
                          .empty)))
                    (.node 80074 (-2)
                      (.node 80014 (-2)
                        (.node 79999 (2)
                          .empty
                          .empty)
                        (.node 80051 (-2)
                          .empty
                          .empty))
                      (.node 80096 (2)
                        (.node 80077 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 80597 (-2)
                  (.node 80320 (-2)
                    (.node 80243 (2)
                      (.node 80194 (2)
                        (.node 80168 (-2)
                          .empty
                          .empty)
                        (.node 80197 (-2)
                          .empty
                          .empty))
                      (.node 80279 (-2)
                        (.node 80256 (2)
                          .empty
                          .empty)
                        (.node 80305 (2)
                          .empty
                          .empty)))
                    (.node 80481 (2)
                      (.node 80436 (2)
                        (.node 80346 (-2)
                          .empty
                          .empty)
                        (.node 80460 (2)
                          .empty
                          .empty))
                      (.node 80573 (-2)
                        (.node 80564 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 80766 (2)
                    (.node 80687 (-2)
                      (.node 80643 (-2)
                        (.node 80634 (2)
                          .empty
                          .empty)
                        (.node 80664 (2)
                          .empty
                          .empty))
                      (.node 80725 (-2)
                        (.node 80696 (2)
                          .empty
                          .empty)
                        (.node 80745 (2)
                          .empty
                          .empty)))
                    (.node 80833 (2)
                      (.node 80799 (-2)
                        (.node 80777 (-2)
                          .empty
                          .empty)
                        (.node 80819 (2)
                          .empty
                          .empty))
                      (.node 80874 (2)
                        (.node 80848 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 81588 (-2)
                (.node 81238 (-2)
                  (.node 81083 (-2)
                    (.node 81014 (2)
                      (.node 80933 (-2)
                        (.node 80924 (2)
                          .empty
                          .empty)
                        (.node 80985 (2)
                          .empty
                          .empty))
                      (.node 81042 (2)
                        (.node 81015 (-2)
                          .empty
                          .empty)
                        (.node 81057 (2)
                          .empty
                          .empty)))
                    (.node 81157 (2)
                      (.node 81113 (2)
                        (.node 81102 (-2)
                          .empty
                          .empty)
                        (.node 81154 (-2)
                          .empty
                          .empty))
                      (.node 81223 (2)
                        (.node 81176 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 81416 (-2)
                    (.node 81293 (-2)
                      (.node 81253 (2)
                        (.node 81250 (-2)
                          .empty
                          .empty)
                        (.node 81272 (2)
                          .empty
                          .empty))
                      (.node 81357 (-2)
                        (.node 81316 (-2)
                          .empty
                          .empty)
                        (.node 81393 (-2)
                          .empty
                          .empty)))
                    (.node 81487 (2)
                      (.node 81445 (2)
                        (.node 81442 (-2)
                          .empty
                          .empty)
                        (.node 81467 (-2)
                          .empty
                          .empty))
                      (.node 81509 (2)
                        (.node 81502 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 82085 (-2)
                  (.node 81861 (2)
                    (.node 81780 (2)
                      (.node 81656 (2)
                        (.node 81633 (2)
                          .empty
                          .empty)
                        (.node 81716 (2)
                          .empty
                          .empty))
                      (.node 81837 (2)
                        (.node 81835 (-2)
                          .empty
                          .empty)
                        (.node 81859 (-2)
                          .empty
                          .empty)))
                    (.node 81980 (-2)
                      (.node 81946 (2)
                        (.node 81873 (2)
                          .empty
                          .empty)
                        (.node 81949 (-2)
                          .empty
                          .empty))
                      (.node 82013 (-2)
                        (.node 82004 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 82258 (4)
                    (.node 82187 (-2)
                      (.node 82148 (2)
                        (.node 82124 (2)
                          .empty
                          .empty)
                        (.node 82160 (2)
                          .empty
                          .empty))
                      (.node 82222 (-2)
                        (.node 82207 (2)
                          .empty
                          .empty)
                        (.node 82242 (2)
                          .empty
                          .empty)))
                    (.node 82313 (-2)
                      (.node 82281 (-2)
                        (.node 82261 (-2)
                          .empty
                          .empty)
                        (.node 82302 (2)
                          .empty
                          .empty))
                      (.node 82353 (-2)
                        (.node 82334 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 83806 (2)
              (.node 83220 (2)
                (.node 82852 (2)
                  (.node 82595 (-2)
                    (.node 82490 (-2)
                      (.node 82451 (-2)
                        (.node 82436 (-2)
                          .empty
                          .empty)
                        (.node 82472 (2)
                          .empty
                          .empty))
                      (.node 82515 (-2)
                        (.node 82492 (2)
                          .empty
                          .empty)
                        (.node 82565 (-2)
                          .empty
                          .empty)))
                    (.node 82791 (-2)
                      (.node 82709 (-2)
                        (.node 82617 (2)
                          .empty
                          .empty)
                        (.node 82790 (2)
                          .empty
                          .empty))
                      (.node 82829 (2)
                        (.node 82818 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 83052 (2)
                    (.node 82971 (2)
                      (.node 82921 (2)
                        (.node 82891 (-2)
                          .empty
                          .empty)
                        (.node 82936 (-2)
                          .empty
                          .empty))
                      (.node 83007 (-2)
                        (.node 83006 (2)
                          .empty
                          .empty)
                        (.node 83039 (-2)
                          .empty
                          .empty)))
                    (.node 83144 (-2)
                      (.node 83131 (-2)
                        (.node 83094 (-2)
                          .empty
                          .empty)
                        (.node 83133 (2)
                          .empty
                          .empty))
                      (.node 83175 (-2)
                        (.node 83174 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 83501 (2)
                  (.node 83406 (-2)
                    (.node 83298 (-2)
                      (.node 83262 (-2)
                        (.node 83243 (-2)
                          .empty
                          .empty)
                        (.node 83273 (2)
                          .empty
                          .empty))
                      (.node 83354 (-2)
                        (.node 83315 (-2)
                          .empty
                          .empty)
                        (.node 83356 (2)
                          .empty
                          .empty)))
                    (.node 83458 (-2)
                      (.node 83430 (-2)
                        (.node 83417 (2)
                          .empty
                          .empty)
                        (.node 83441 (2)
                          .empty
                          .empty))
                      (.node 83484 (2)
                        (.node 83461 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 83686 (2)
                    (.node 83617 (-2)
                      (.node 83553 (2)
                        (.node 83525 (2)
                          .empty
                          .empty)
                        (.node 83600 (-2)
                          .empty
                          .empty))
                      (.node 83662 (2)
                        (.node 83647 (-4)
                          .empty
                          .empty)
                        (.node 83671 (-2)
                          .empty
                          .empty)))
                    (.node 83761 (-2)
                      (.node 83704 (2)
                        (.node 83689 (-2)
                          .empty
                          .empty)
                        (.node 83747 (-2)
                          .empty
                          .empty))
                      (.node 83791 (-2)
                        (.node 83776 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 84684 (2)
                (.node 84173 (2)
                  (.node 83944 (-2)
                    (.node 83880 (2)
                      (.node 83863 (2)
                        (.node 83826 (-2)
                          .empty
                          .empty)
                        (.node 83878 (-2)
                          .empty
                          .empty))
                      (.node 83912 (2)
                        (.node 83903 (-2)
                          .empty
                          .empty)
                        (.node 83929 (2)
                          .empty
                          .empty)))
                    (.node 84101 (2)
                      (.node 83975 (-2)
                        (.node 83952 (2)
                          .empty
                          .empty)
                        (.node 84003 (2)
                          .empty
                          .empty))
                      (.node 84164 (-2)
                        (.node 84123 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 84440 (-2)
                    (.node 84379 (2)
                      (.node 84328 (-2)
                        (.node 84313 (2)
                          .empty
                          .empty)
                        (.node 84348 (2)
                          .empty
                          .empty))
                      (.node 84395 (2)
                        (.node 84381 (-2)
                          .empty
                          .empty)
                        (.node 84420 (2)
                          .empty
                          .empty)))
                    (.node 84575 (2)
                      (.node 84538 (2)
                        (.node 84515 (2)
                          .empty
                          .empty)
                        (.node 84541 (-2)
                          .empty
                          .empty))
                      (.node 84641 (-2)
                        (.node 84588 (-2)
                          .empty
                          .empty)
                        .empty))))
                (.node 85068 (2)
                  (.node 84903 (-2)
                    (.node 84849 (2)
                      (.node 84788 (2)
                        (.node 84762 (-2)
                          .empty
                          .empty)
                        (.node 84828 (2)
                          .empty
                          .empty))
                      (.node 84885 (-2)
                        (.node 84883 (2)
                          .empty
                          .empty)
                        (.node 84902 (2)
                          .empty
                          .empty)))
                    (.node 84983 (2)
                      (.node 84927 (-2)
                        (.node 84926 (2)
                          .empty
                          .empty)
                        (.node 84960 (-2)
                          .empty
                          .empty))
                      (.node 85044 (2)
                        (.node 85026 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 85246 (-2)
                    (.node 85183 (-2)
                      (.node 85136 (2)
                        (.node 85100 (2)
                          .empty
                          .empty)
                        (.node 85153 (2)
                          .empty
                          .empty))
                      (.node 85222 (2)
                        (.node 85207 (-2)
                          .empty
                          .empty)
                        (.node 85231 (2)
                          .empty
                          .empty)))
                    (.node 85303 (2)
                      (.node 85252 (2)
                        (.node 85250 (-2)
                          .empty
                          .empty)
                        (.node 85290 (2)
                          .empty
                          .empty))
                      (.node 85322 (2)
                        (.node 85318 (-2)
                          .empty
                          .empty)
                        .empty))))))))
        (.node 91171 (-2)
          (.node 88298 (2)
            (.node 86652 (2)
              (.node 86005 (2)
                (.node 85698 (-2)
                  (.node 85485 (-2)
                    (.node 85394 (2)
                      (.node 85375 (-2)
                        (.node 85347 (2)
                          .empty
                          .empty)
                        (.node 85390 (2)
                          .empty
                          .empty))
                      (.node 85449 (2)
                        (.node 85396 (-2)
                          .empty
                          .empty)
                        (.node 85483 (2)
                          .empty
                          .empty)))
                    (.node 85614 (-2)
                      (.node 85570 (-2)
                        (.node 85548 (-2)
                          .empty
                          .empty)
                        (.node 85573 (2)
                          .empty
                          .empty))
                      (.node 85635 (2)
                        (.node 85625 (2)
                          .empty
                          .empty)
                        (.node 85661 (-2)
                          .empty
                          .empty))))
                  (.node 85892 (-2)
                    (.node 85802 (2)
                      (.node 85786 (-2)
                        (.node 85715 (-2)
                          .empty
                          .empty)
                        (.node 85789 (2)
                          .empty
                          .empty))
                      (.node 85855 (2)
                        (.node 85804 (-2)
                          .empty
                          .empty)
                        (.node 85870 (-2)
                          .empty
                          .empty)))
                    (.node 85953 (-2)
                      (.node 85909 (-2)
                        (.node 85906 (2)
                          .empty
                          .empty)
                        (.node 85928 (-2)
                          .empty
                          .empty))
                      (.node 86002 (-2)
                        (.node 85979 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 86297 (-2)
                  (.node 86165 (-2)
                    (.node 86096 (2)
                      (.node 86066 (2)
                        (.node 86049 (-2)
                          .empty
                          .empty)
                        (.node 86068 (-2)
                          .empty
                          .empty))
                      (.node 86129 (-2)
                        (.node 86118 (2)
                          .empty
                          .empty)
                        (.node 86147 (-2)
                          .empty
                          .empty)))
                    (.node 86234 (2)
                      (.node 86206 (-2)
                        (.node 86191 (2)
                          .empty
                          .empty)
                        (.node 86220 (2)
                          .empty
                          .empty))
                      (.node 86286 (4)
                        (.node 86236 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 86518 (2)
                    (.node 86380 (2)
                      (.node 86375 (-2)
                        (.node 86333 (-2)
                          .empty
                          .empty)
                        (.node 86378 (-2)
                          .empty
                          .empty))
                      (.node 86427 (-2)
                        (.node 86408 (-2)
                          .empty
                          .empty)
                        (.node 86459 (-2)
                          .empty
                          .empty)))
                    (.node 86613 (-2)
                      (.node 86562 (-2)
                        (.node 86536 (-2)
                          .empty
                          .empty)
                        (.node 86611 (2)
                          .empty
                          .empty))
                      (.node 86631 (2)
                        (.node 86630 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 87233 (-2)
                (.node 86922 (2)
                  (.node 86794 (-2)
                    (.node 86742 (-2)
                      (.node 86702 (2)
                        (.node 86676 (-2)
                          .empty
                          .empty)
                        (.node 86703 (-2)
                          .empty
                          .empty))
                      (.node 86766 (2)
                        (.node 86753 (2)
                          .empty
                          .empty)
                        (.node 86777 (-2)
                          .empty
                          .empty)))
                    (.node 86849 (-2)
                      (.node 86820 (-2)
                        (.node 86797 (2)
                          .empty
                          .empty)
                        (.node 86838 (2)
                          .empty
                          .empty))
                      (.node 86884 (2)
                        (.node 86882 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 87107 (2)
                    (.node 87050 (2)
                      (.node 87006 (-2)
                        (.node 86996 (2)
                          .empty
                          .empty)
                        (.node 87017 (2)
                          .empty
                          .empty))
                      (.node 87072 (2)
                        (.node 87052 (-2)
                          .empty
                          .empty)
                        (.node 87095 (-2)
                          .empty
                          .empty)))
                    (.node 87192 (-2)
                      (.node 87124 (-2)
                        (.node 87122 (2)
                          .empty
                          .empty)
                        (.node 87162 (2)
                          .empty
                          .empty))
                      (.node 87222 (2)
                        (.node 87215 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 87704 (2)
                  (.node 87436 (-2)
                    (.node 87339 (-2)
                      (.node 87273 (-2)
                        (.node 87243 (-2)
                          .empty
                          .empty)
                        (.node 87296 (-2)
                          .empty
                          .empty))
                      (.node 87392 (2)
                        (.node 87369 (-2)
                          .empty
                          .empty)
                        (.node 87434 (2)
                          .empty
                          .empty)))
                    (.node 87615 (2)
                      (.node 87587 (2)
                        (.node 87524 (-2)
                          .empty
                          .empty)
                        (.node 87614 (-2)
                          .empty
                          .empty))
                      (.node 87692 (2)
                        (.node 87629 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 88039 (2)
                    (.node 87911 (2)
                      (.node 87822 (2)
                        (.node 87749 (2)
                          .empty
                          .empty)
                        (.node 87869 (2)
                          .empty
                          .empty))
                      (.node 87971 (-2)
                        (.node 87954 (-2)
                          .empty
                          .empty)
                        (.node 87987 (-2)
                          .empty
                          .empty)))
                    (.node 88156 (2)
                      (.node 88098 (2)
                        (.node 88072 (2)
                          .empty
                          .empty)
                        (.node 88154 (-2)
                          .empty
                          .empty))
                      (.node 88218 (2)
                        (.node 88184 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 89844 (-2)
              (.node 89067 (2)
                (.node 88640 (-2)
                  (.node 88524 (-2)
                    (.node 88372 (2)
                      (.node 88355 (-2)
                        (.node 88300 (-2)
                          .empty
                          .empty)
                        (.node 88370 (-2)
                          .empty
                          .empty))
                      (.node 88494 (2)
                        (.node 88449 (-2)
                          .empty
                          .empty)
                        (.node 88505 (-2)
                          .empty
                          .empty)))
                    (.node 88577 (2)
                      (.node 88549 (-2)
                        (.node 88546 (2)
                          .empty
                          .empty)
                        (.node 88566 (-2)
                          .empty
                          .empty))
                      (.node 88606 (-2)
                        (.node 88591 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 88794 (2)
                    (.node 88710 (-2)
                      (.node 88678 (2)
                        (.node 88663 (-2)
                          .empty
                          .empty)
                        (.node 88691 (-2)
                          .empty
                          .empty))
                      (.node 88762 (2)
                        (.node 88721 (2)
                          .empty
                          .empty)
                        (.node 88765 (-2)
                          .empty
                          .empty)))
                    (.node 88904 (-2)
                      (.node 88835 (2)
                        (.node 88812 (2)
                          .empty
                          .empty)
                        (.node 88877 (-2)
                          .empty
                          .empty))
                      (.node 89048 (2)
                        (.node 88929 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 89504 (-2)
                  (.node 89346 (2)
                    (.node 89156 (-2)
                      (.node 89113 (2)
                        (.node 89100 (2)
                          .empty
                          .empty)
                        (.node 89128 (-2)
                          .empty
                          .empty))
                      (.node 89261 (2)
                        (.node 89219 (2)
                          .empty
                          .empty)
                        (.node 89313 (2)
                          .empty
                          .empty)))
                    (.node 89455 (2)
                      (.node 89431 (-2)
                        (.node 89412 (-2)
                          .empty
                          .empty)
                        (.node 89446 (2)
                          .empty
                          .empty))
                      (.node 89483 (-2)
                        (.node 89470 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 89653 (2)
                    (.node 89597 (2)
                      (.node 89553 (2)
                        (.node 89538 (-2)
                          .empty
                          .empty)
                        (.node 89588 (-2)
                          .empty
                          .empty))
                      (.node 89629 (-2)
                        (.node 89626 (2)
                          .empty
                          .empty)
                        (.node 89650 (-2)
                          .empty
                          .empty)))
                    (.node 89738 (-2)
                      (.node 89705 (2)
                        (.node 89694 (-2)
                          .empty
                          .empty)
                        (.node 89721 (-2)
                          .empty
                          .empty))
                      (.node 89811 (-2)
                        (.node 89740 (2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 90542 (2)
                (.node 90165 (-2)
                  (.node 90033 (-2)
                    (.node 89909 (-2)
                      (.node 89899 (-2)
                        (.node 89876 (-2)
                          .empty
                          .empty)
                        (.node 89901 (2)
                          .empty
                          .empty))
                      (.node 89981 (2)
                        (.node 89948 (2)
                          .empty
                          .empty)
                        (.node 90009 (2)
                          .empty
                          .empty)))
                    (.node 90116 (-2)
                      (.node 90063 (-2)
                        (.node 90062 (2)
                          .empty
                          .empty)
                        (.node 90084 (2)
                          .empty
                          .empty))
                      (.node 90163 (2)
                        (.node 90134 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 90357 (-2)
                    (.node 90278 (-2)
                      (.node 90205 (2)
                        (.node 90188 (2)
                          .empty
                          .empty)
                        (.node 90236 (2)
                          .empty
                          .empty))
                      (.node 90319 (2)
                        (.node 90279 (2)
                          .empty
                          .empty)
                        (.node 90334 (-2)
                          .empty
                          .empty)))
                    (.node 90450 (2)
                      (.node 90396 (2)
                        (.node 90362 (2)
                          .empty
                          .empty)
                        (.node 90420 (-2)
                          .empty
                          .empty))
                      (.node 90512 (2)
                        (.node 90465 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 90818 (2)
                  (.node 90667 (2)
                    (.node 90582 (2)
                      (.node 90552 (-2)
                        (.node 90543 (-2)
                          .empty
                          .empty)
                        (.node 90575 (2)
                          .empty
                          .empty))
                      (.node 90605 (2)
                        (.node 90593 (-2)
                          .empty
                          .empty)
                        (.node 90635 (2)
                          .empty
                          .empty)))
                    (.node 90724 (-2)
                      (.node 90690 (-2)
                        (.node 90669 (-2)
                          .empty
                          .empty)
                        (.node 90722 (2)
                          .empty
                          .empty))
                      (.node 90801 (-2)
                        (.node 90749 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 90964 (2)
                    (.node 90912 (-2)
                      (.node 90845 (-2)
                        (.node 90820 (-2)
                          .empty
                          .empty)
                        (.node 90875 (-2)
                          .empty
                          .empty))
                      (.node 90945 (2)
                        (.node 90935 (2)
                          .empty
                          .empty)
                        (.node 90962 (-2)
                          .empty
                          .empty)))
                    (.node 91092 (-2)
                      (.node 91035 (2)
                        (.node 91026 (2)
                          .empty
                          .empty)
                        (.node 91067 (2)
                          .empty
                          .empty))
                      (.node 91148 (-2)
                        (.node 91109 (2)
                          .empty
                          .empty)
                        .empty)))))))
          (.node 94896 (-2)
            (.node 92842 (-2)
              (.node 91855 (2)
                (.node 91580 (-2)
                  (.node 91416 (-2)
                    (.node 91256 (-2)
                      (.node 91226 (-2)
                        (.node 91173 (2)
                          .empty
                          .empty)
                        (.node 91228 (2)
                          .empty
                          .empty))
                      (.node 91376 (2)
                        (.node 91356 (2)
                          .empty
                          .empty)
                        (.node 91395 (2)
                          .empty
                          .empty)))
                    (.node 91490 (-2)
                      (.node 91458 (2)
                        (.node 91439 (2)
                          .empty
                          .empty)
                        (.node 91475 (-2)
                          .empty
                          .empty))
                      (.node 91520 (-2)
                        (.node 91492 (2)
                          .empty
                          .empty)
                        (.node 91539 (-2)
                          .empty
                          .empty))))
                  (.node 91761 (2)
                    (.node 91699 (2)
                      (.node 91641 (-2)
                        (.node 91613 (2)
                          .empty
                          .empty)
                        (.node 91671 (-2)
                          .empty
                          .empty))
                      (.node 91724 (-2)
                        (.node 91701 (-2)
                          .empty
                          .empty)
                        (.node 91741 (-2)
                          .empty
                          .empty)))
                    (.node 91813 (-2)
                      (.node 91798 (-2)
                        (.node 91783 (2)
                          .empty
                          .empty)
                        (.node 91810 (2)
                          .empty
                          .empty))
                      (.node 91828 (-2)
                        (.node 91826 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 92251 (2)
                  (.node 92003 (-2)
                    (.node 91900 (-4)
                      (.node 91891 (-2)
                        (.node 91870 (-2)
                          .empty
                          .empty)
                        (.node 91898 (2)
                          .empty
                          .empty))
                      (.node 91952 (2)
                        (.node 91932 (-2)
                          .empty
                          .empty)
                        (.node 91973 (-2)
                          .empty
                          .empty)))
                    (.node 92145 (-2)
                      (.node 92094 (2)
                        (.node 92045 (-2)
                          .empty
                          .empty)
                        (.node 92105 (-2)
                          .empty
                          .empty))
                      (.node 92211 (2)
                        (.node 92193 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 92566 (-2)
                    (.node 92396 (-2)
                      (.node 92289 (-2)
                        (.node 92253 (-2)
                          .empty
                          .empty)
                        (.node 92345 (2)
                          .empty
                          .empty))
                      (.node 92423 (4)
                        (.node 92400 (-2)
                          .empty
                          .empty)
                        (.node 92459 (-2)
                          .empty
                          .empty)))
                    (.node 92684 (2)
                      (.node 92595 (2)
                        (.node 92569 (-2)
                          .empty
                          .empty)
                        (.node 92652 (2)
                          .empty
                          .empty))
                      (.node 92720 (2)
                        (.node 92700 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 93588 (2)
                (.node 93189 (-2)
                  (.node 93051 (-2)
                    (.node 92951 (-2)
                      (.node 92892 (-2)
                        (.node 92845 (2)
                          .empty
                          .empty)
                        (.node 92928 (2)
                          .empty
                          .empty))
                      (.node 93000 (-2)
                        (.node 92963 (-2)
                          .empty
                          .empty)
                        (.node 93023 (2)
                          .empty
                          .empty)))
                    (.node 93117 (-2)
                      (.node 93095 (2)
                        (.node 93072 (-2)
                          .empty
                          .empty)
                        (.node 93115 (2)
                          .empty
                          .empty))
                      (.node 93187 (2)
                        (.node 93164 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 93356 (2)
                    (.node 93270 (2)
                      (.node 93209 (2)
                        (.node 93198 (-2)
                          .empty
                          .empty)
                        (.node 93225 (-2)
                          .empty
                          .empty))
                      (.node 93297 (-2)
                        (.node 93281 (-2)
                          .empty
                          .empty)
                        (.node 93330 (2)
                          .empty
                          .empty)))
                    (.node 93480 (-2)
                      (.node 93414 (-2)
                        (.node 93392 (2)
                          .empty
                          .empty)
                        (.node 93425 (2)
                          .empty
                          .empty))
                      (.node 93564 (-2)
                        (.node 93503 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 94131 (-2)
                  (.node 93932 (2)
                    (.node 93723 (2)
                      (.node 93629 (2)
                        (.node 93603 (-2)
                          .empty
                          .empty)
                        (.node 93675 (2)
                          .empty
                          .empty))
                      (.node 93827 (2)
                        (.node 93753 (-2)
                          .empty
                          .empty)
                        (.node 93870 (2)
                          .empty
                          .empty)))
                    (.node 94054 (2)
                      (.node 93987 (-2)
                        (.node 93936 (-2)
                          .empty
                          .empty)
                        (.node 94039 (-2)
                          .empty
                          .empty))
                      (.node 94105 (2)
                        (.node 94087 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 94493 (2)
                    (.node 94253 (-2)
                      (.node 94209 (2)
                        (.node 94181 (2)
                          .empty
                          .empty)
                        (.node 94229 (-2)
                          .empty
                          .empty))
                      (.node 94311 (-2)
                        (.node 94310 (2)
                          .empty
                          .empty)
                        (.node 94424 (2)
                          .empty
                          .empty)))
                    (.node 94836 (2)
                      (.node 94685 (2)
                        (.node 94589 (-2)
                          .empty
                          .empty)
                        (.node 94757 (2)
                          .empty
                          .empty))
                      (.node 94877 (-2)
                        (.node 94851 (-2)
                          .empty
                          .empty)
                        .empty))))))
            (.node 96610 (2)
              (.node 95768 (2)
                (.node 95369 (2)
                  (.node 95163 (2)
                    (.node 94991 (2)
                      (.node 94923 (-2)
                        (.node 94919 (2)
                          .empty
                          .empty)
                        (.node 94968 (-2)
                          .empty
                          .empty))
                      (.node 95123 (2)
                        (.node 95091 (2)
                          .empty
                          .empty)
                        (.node 95141 (-2)
                          .empty
                          .empty)))
                    (.node 95313 (2)
                      (.node 95197 (-2)
                        (.node 95194 (2)
                          .empty
                          .empty)
                        (.node 95274 (2)
                          .empty
                          .empty))
                      (.node 95358 (-2)
                        (.node 95331 (-2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 95564 (2)
                    (.node 95466 (-2)
                      (.node 95401 (2)
                        (.node 95387 (-2)
                          .empty
                          .empty)
                        (.node 95416 (-2)
                          .empty
                          .empty))
                      (.node 95527 (-2)
                        (.node 95505 (2)
                          .empty
                          .empty)
                        (.node 95542 (2)
                          .empty
                          .empty)))
                    (.node 95651 (2)
                      (.node 95595 (-2)
                        (.node 95579 (2)
                          .empty
                          .empty)
                        (.node 95624 (-2)
                          .empty
                          .empty))
                      (.node 95739 (2)
                        (.node 95730 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 96141 (2)
                  (.node 96001 (-2)
                    (.node 95928 (-2)
                      (.node 95807 (-2)
                        (.node 95784 (2)
                          .empty
                          .empty)
                        (.node 95864 (2)
                          .empty
                          .empty))
                      (.node 95970 (-2)
                        (.node 95951 (2)
                          .empty
                          .empty)
                        (.node 95994 (2)
                          .empty
                          .empty)))
                    (.node 96081 (2)
                      (.node 96042 (-2)
                        (.node 96016 (2)
                          .empty
                          .empty)
                        (.node 96056 (2)
                          .empty
                          .empty))
                      (.node 96139 (-2)
                        (.node 96116 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 96323 (2)
                    (.node 96253 (-2)
                      (.node 96183 (-2)
                        (.node 96164 (2)
                          .empty
                          .empty)
                        (.node 96221 (-2)
                          .empty
                          .empty))
                      (.node 96295 (2)
                        (.node 96275 (2)
                          .empty
                          .empty)
                        (.node 96310 (-2)
                          .empty
                          .empty)))
                    (.node 96441 (2)
                      (.node 96403 (2)
                        (.node 96339 (2)
                          .empty
                          .empty)
                        (.node 96410 (2)
                          .empty
                          .empty))
                      (.node 96564 (2)
                        (.node 96474 (-2)
                          .empty
                          .empty)
                        .empty)))))
              (.node 97508 (-2)
                (.node 97092 (-2)
                  (.node 96848 (2)
                    (.node 96708 (2)
                      (.node 96660 (-2)
                        (.node 96613 (-2)
                          .empty
                          .empty)
                        (.node 96675 (2)
                          .empty
                          .empty))
                      (.node 96791 (2)
                        (.node 96768 (-2)
                          .empty
                          .empty)
                        (.node 96801 (-2)
                          .empty
                          .empty)))
                    (.node 97027 (-2)
                      (.node 96924 (-2)
                        (.node 96869 (-2)
                          .empty
                          .empty)
                        (.node 96987 (2)
                          .empty
                          .empty))
                      (.node 97037 (-2)
                        (.node 97029 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 97228 (2)
                    (.node 97184 (-2)
                      (.node 97146 (2)
                        (.node 97122 (-2)
                          .empty
                          .empty)
                        (.node 97163 (2)
                          .empty
                          .empty))
                      (.node 97222 (2)
                        (.node 97207 (-2)
                          .empty
                          .empty)
                        (.node 97226 (-2)
                          .empty
                          .empty)))
                    (.node 97412 (-2)
                      (.node 97280 (-2)
                        (.node 97259 (-2)
                          .empty
                          .empty)
                        (.node 97299 (-2)
                          .empty
                          .empty))
                      (.node 97461 (-2)
                        (.node 97459 (2)
                          .empty
                          .empty)
                        .empty))))
                (.node 97824 (2)
                  (.node 97656 (-2)
                    (.node 97572 (2)
                      (.node 97550 (2)
                        (.node 97524 (-2)
                          .empty
                          .empty)
                        (.node 97551 (-2)
                          .empty
                          .empty))
                      (.node 97619 (-2)
                        (.node 97589 (-2)
                          .empty
                          .empty)
                        (.node 97635 (-2)
                          .empty
                          .empty)))
                    (.node 97757 (2)
                      (.node 97683 (-2)
                        (.node 97679 (2)
                          .empty
                          .empty)
                        (.node 97718 (-2)
                          .empty
                          .empty))
                      (.node 97803 (2)
                        (.node 97789 (2)
                          .empty
                          .empty)
                        .empty)))
                  (.node 98000 (-2)
                    (.node 97939 (4)
                      (.node 97851 (2)
                        (.node 97847 (-2)
                          .empty
                          .empty)
                        (.node 97883 (2)
                          .empty
                          .empty))
                      (.node 97946 (-2)
                        (.node 97941 (-2)
                          .empty
                          .empty)
                        (.node 97977 (-2)
                          .empty
                          .empty)))
                    (.node 98192 (2)
                      (.node 98056 (-2)
                        (.node 98041 (2)
                          .empty
                          .empty)
                        (.node 98106 (-2)
                          .empty
                          .empty))
                      (.node 98240 (-2)
                        (.node 98228 (-2)
                          .empty
                          .empty)
                        .empty)))))))))))

set_option maxHeartbeats 8000000 in
-- The exact structural equality unfolds all3856 original keys and signed source values.
/-- The literal cache is exactly the entire original index tree mapped by its original fields. -/
theorem generatedNinth_lower_middle_short_key_value_tree_actual :
    generatedNinthLowerMiddleShortKeyValueTree =
      generatedNinthLowerMiddleShortTree.mapKeyValue
        generatedNinthLowerMiddleShortKey generatedNinthLowerMiddleShortNumerator := by
  rfl

/-- The complete original middle source coefficient through its verified direct key/value tree. -/
def generatedNinthLowerMiddleShortCachedCoefficient (r : GriessShortIndex) : ℤ :=
  generatedNinthLowerMiddleShortKeyValueTree.lookup (generatedNinthLowerShortAddress r)

/-- Every preferred source coordinate, including all zeros, retains its original middle value. -/
theorem generatedNinth_lower_middle_short_cached_coefficient_actual (r : GriessShortIndex) :
    generatedNinthLowerMiddleShortCachedCoefficient r =
      generatedNinthLowerMiddleShortCoefficient r := by
  unfold generatedNinthLowerMiddleShortCachedCoefficient
  rw [generatedNinth_lower_middle_short_key_value_tree_actual,
    GeneratedNinthIncomingTree.lookup_mapKeyValue]
  unfold generatedNinthLowerMiddleShortCoefficient
  cases generatedNinthLowerMiddleShortTree.lookup generatedNinthLowerMiddleShortKey
    (generatedNinthLowerShortAddress r) <;> rfl

/-- Every original odd coordinate uses the same complete direct key/value source cache. -/
def generatedNinthLowerIncomingCachedCoefficient (d : Fin 2048) (i : Fin 24) : ℤ :=
  generatedNinthLowerMiddleShortCachedCoefficient (Sum.inr (Sum.inr (d, i)))

/-- All original odd-label and spatial-column source values retain their complete signed values. -/
theorem generatedNinth_lower_incoming_cached_coefficient_actual (d : Fin 2048) (i : Fin 24) :
    generatedNinthLowerIncomingCachedCoefficient d i = generatedNinthLowerIncomingCoefficient d i :=
  generatedNinth_lower_middle_short_cached_coefficient_actual _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
