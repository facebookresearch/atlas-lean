/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal chronological right-coset proof data from actual original-source consequences. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawCosetPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Exact literal coset claims and source or chronological right-context moves in this interval. -/
def y422CosetData05 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[243, 13], [241], [
      .equation 157 false false
        []
        [13],
      .equation 10 false false
        [241]
        []]⟩,
    ⟨[241, 13], [243], [
      .equation 157 true false
        []
        []]⟩,
    ⟨[243, 9], [243, 9], [
]⟩,
    ⟨[243], [243], [
]⟩,
    ⟨[243, 9], [243], [
      .prior 642 false [],
      .prior 641 true [9],
      .equation 11 false false
        [241, 8]
        [12],
      .equation 1 true false
        [241, 8]
        [12],
      .prior 639 false [12],
      .equation 10 true false
        [241, 12]
        [],
      .equation 157 true false
        []
        [],
      .prior 643 false []]⟩,
    ⟨[245, 1], [243], [
      .equation 158 false false
        []
        [1],
      .equation 2 false false
        [243]
        []]⟩,
    ⟨[243, 1], [245], [
      .equation 158 true false
        []
        []]⟩,
    ⟨[245, 9], [245, 9], [
]⟩,
    ⟨[245], [245], [
]⟩,
    ⟨[245, 9], [245], [
      .prior 647 false [],
      .prior 646 true [9],
      .equation 3 false false
        [243]
        [8, 0],
      .equation 1 true false
        [243, 8]
        [0],
      .prior 644 false [0],
      .equation 2 true false
        [243, 0]
        [],
      .equation 158 true false
        []
        [],
      .prior 648 false []]⟩,
    ⟨[247, 15], [245], [
      .equation 159 false false
        []
        [15],
      .equation 12 false false
        [245]
        []]⟩,
    ⟨[245, 15], [247], [
      .equation 159 true false
        []
        []]⟩,
    ⟨[247, 9], [247, 9], [
]⟩,
    ⟨[247], [247], [
]⟩,
    ⟨[247, 9], [247], [
      .prior 652 false [],
      .prior 651 true [9],
      .equation 13 false false
        [245, 8]
        [14],
      .equation 1 true false
        [245, 8]
        [14],
      .prior 649 false [14],
      .equation 12 true false
        [245, 14]
        [],
      .equation 159 true false
        []
        [],
      .prior 653 false []]⟩,
    ⟨[249, 17], [247], [
      .equation 160 false false
        []
        [17],
      .equation 14 false false
        [247]
        []]⟩,
    ⟨[247, 17], [249], [
      .equation 160 true false
        []
        []]⟩,
    ⟨[249, 9], [249, 9], [
]⟩,
    ⟨[249], [249], [
]⟩,
    ⟨[249, 9], [249], [
      .prior 657 false [],
      .prior 656 true [9],
      .equation 15 false false
        [247, 8]
        [16],
      .equation 1 true false
        [247, 8]
        [16],
      .prior 654 false [16],
      .equation 14 true false
        [247, 16]
        [],
      .equation 160 true false
        []
        [],
      .prior 658 false []]⟩,
    ⟨[251, 1], [249], [
      .equation 161 false false
        []
        [1],
      .equation 2 false false
        [249]
        []]⟩,
    ⟨[249, 1], [251], [
      .equation 161 true false
        []
        []]⟩,
    ⟨[251, 9], [251, 9], [
]⟩,
    ⟨[251], [251], [
]⟩,
    ⟨[251, 9], [251], [
      .prior 662 false [],
      .prior 661 true [9],
      .equation 3 false false
        [249]
        [8, 0],
      .equation 1 true false
        [249, 8]
        [0],
      .prior 659 false [0],
      .equation 2 true false
        [249, 0]
        [],
      .equation 161 true false
        []
        [],
      .prior 663 false []]⟩,
    ⟨[253, 3], [251], [
      .equation 162 false false
        []
        [3],
      .equation 4 false false
        [251]
        []]⟩,
    ⟨[251, 3], [253], [
      .equation 162 true false
        []
        []]⟩,
    ⟨[253, 9], [253, 9], [
]⟩,
    ⟨[253], [253], [
]⟩,
    ⟨[253, 9], [253], [
      .prior 667 false [],
      .prior 666 true [9],
      .equation 5 false false
        [251]
        [8, 2],
      .equation 1 true false
        [251, 8]
        [2],
      .prior 664 false [2],
      .equation 4 true false
        [251, 2]
        [],
      .equation 162 true false
        []
        [],
      .prior 668 false []]⟩,
    ⟨[255, 5], [253], [
      .equation 163 false false
        []
        [5],
      .equation 6 false false
        [253]
        []]⟩,
    ⟨[253, 5], [255], [
      .equation 163 true false
        []
        []]⟩,
    ⟨[255, 9], [255, 9], [
]⟩,
    ⟨[255], [255], [
]⟩,
    ⟨[255, 9], [255], [
      .prior 672 false [],
      .prior 671 true [9],
      .equation 7 false false
        [253]
        [8, 4],
      .equation 1 true false
        [253, 8]
        [4],
      .prior 669 false [4],
      .equation 6 true false
        [253, 4]
        [],
      .equation 163 true false
        []
        [],
      .prior 673 false []]⟩,
    ⟨[257, 1], [255], [
      .equation 164 false false
        []
        [1],
      .equation 2 false false
        [255]
        []]⟩,
    ⟨[255, 1], [257], [
      .equation 164 true false
        []
        []]⟩,
    ⟨[257, 9], [257, 9], [
]⟩,
    ⟨[257], [257], [
]⟩,
    ⟨[257, 9], [257], [
      .prior 677 false [],
      .prior 676 true [9],
      .equation 3 false false
        [255]
        [8, 0],
      .equation 1 true false
        [255, 8]
        [0],
      .prior 674 false [0],
      .equation 2 true false
        [255, 0]
        [],
      .equation 164 true false
        []
        [],
      .prior 678 false []]⟩,
    ⟨[259, 11], [257], [
      .equation 165 false false
        []
        [11],
      .equation 8 false false
        [257]
        []]⟩,
    ⟨[257, 11], [259], [
      .equation 165 true false
        []
        []]⟩,
    ⟨[259], [259], [
]⟩,
    ⟨[259, 9], [259], [
      .prior 681 true [9],
      .equation 9 false false
        [257, 8]
        [10],
      .equation 1 true false
        [257, 8]
        [10],
      .prior 679 false [10],
      .equation 8 true false
        [257, 10]
        [],
      .equation 165 true false
        []
        [],
      .prior 682 false []]⟩,
    ⟨[261, 13], [259], [
      .equation 166 false false
        []
        [13],
      .equation 10 false false
        [259]
        []]⟩,
    ⟨[261, 9], [261, 9], [
]⟩,
    ⟨[261], [261], [
]⟩,
    ⟨[261, 9], [261], [
      .prior 685 false [],
      .equation 166 false false
        []
        [9],
      .equation 11 false false
        [259, 8]
        [12],
      .equation 1 true false
        [259, 8]
        [12],
      .prior 683 false [12],
      .equation 10 true false
        [259, 12]
        [],
      .equation 166 true false
        []
        [],
      .prior 686 false []]⟩,
    ⟨[263, 1], [261], [
      .equation 167 false false
        []
        [1],
      .equation 2 false false
        [261]
        []]⟩,
    ⟨[261, 1], [263], [
      .equation 167 true false
        []
        []]⟩,
    ⟨[263, 9], [263, 9], [
]⟩,
    ⟨[263], [263], [
]⟩,
    ⟨[263, 9], [263], [
      .prior 690 false [],
      .prior 689 true [9],
      .equation 3 false false
        [261]
        [8, 0],
      .equation 1 true false
        [261, 8]
        [0],
      .prior 687 false [0],
      .equation 2 true false
        [261, 0]
        [],
      .equation 167 true false
        []
        [],
      .prior 691 false []]⟩,
    ⟨[265, 15], [263], [
      .equation 168 false false
        []
        [15],
      .equation 12 false false
        [263]
        []]⟩,
    ⟨[263, 15], [265], [
      .equation 168 true false
        []
        []]⟩,
    ⟨[265], [265], [
]⟩,
    ⟨[265, 9], [265], [
      .prior 694 true [9],
      .equation 13 false false
        [263, 8]
        [14],
      .equation 1 true false
        [263, 8]
        [14],
      .prior 692 false [14],
      .equation 12 true false
        [263, 14]
        [],
      .equation 168 true false
        []
        [],
      .prior 695 false []]⟩,
    ⟨[267, 17], [265], [
      .equation 169 false false
        []
        [17],
      .equation 14 false false
        [265]
        []]⟩,
    ⟨[267, 9], [267, 9], [
]⟩,
    ⟨[267], [267], [
]⟩,
    ⟨[267, 9], [267], [
      .prior 698 false [],
      .equation 169 false false
        []
        [9],
      .equation 15 false false
        [265, 8]
        [16],
      .equation 1 true false
        [265, 8]
        [16],
      .prior 696 false [16],
      .equation 14 true false
        [265, 16]
        [],
      .equation 169 true false
        []
        [],
      .prior 699 false []]⟩,
    ⟨[269, 1], [267], [
      .equation 170 false false
        []
        [1],
      .equation 2 false false
        [267]
        []]⟩,
    ⟨[267, 1], [269], [
      .equation 170 true false
        []
        []]⟩,
    ⟨[269, 9], [269, 9], [
]⟩,
    ⟨[269], [269], [
]⟩,
    ⟨[269, 9], [269], [
      .prior 703 false [],
      .prior 702 true [9],
      .equation 3 false false
        [267]
        [8, 0],
      .equation 1 true false
        [267, 8]
        [0],
      .prior 700 false [0],
      .equation 2 true false
        [267, 0]
        [],
      .equation 170 true false
        []
        [],
      .prior 704 false []]⟩,
    ⟨[271, 3], [269], [
      .equation 171 false false
        []
        [3],
      .equation 4 false false
        [269]
        []]⟩,
    ⟨[269, 3], [271], [
      .equation 171 true false
        []
        []]⟩,
    ⟨[271], [271], [
]⟩,
    ⟨[271, 9], [271], [
      .prior 707 true [9],
      .equation 5 false false
        [269]
        [8, 2],
      .equation 1 true false
        [269, 8]
        [2],
      .prior 705 false [2],
      .equation 4 true false
        [269, 2]
        [],
      .equation 171 true false
        []
        [],
      .prior 708 false []]⟩,
    ⟨[273, 5], [271], [
      .equation 172 false false
        []
        [5],
      .equation 6 false false
        [271]
        []]⟩,
    ⟨[273, 9], [273, 9], [
]⟩,
    ⟨[273], [273], [
]⟩,
    ⟨[273, 9], [273], [
      .prior 711 false [],
      .equation 172 false false
        []
        [9],
      .equation 7 false false
        [271]
        [8, 4],
      .equation 1 true false
        [271, 8]
        [4],
      .prior 709 false [4],
      .equation 6 true false
        [271, 4]
        [],
      .equation 172 true false
        []
        [],
      .prior 712 false []]⟩,
    ⟨[275, 1], [273], [
      .equation 173 false false
        []
        [1],
      .equation 2 false false
        [273]
        []]⟩,
    ⟨[273, 1], [275], [
      .equation 173 true false
        []
        []]⟩,
    ⟨[275, 9], [275, 9], [
]⟩,
    ⟨[275], [275], [
]⟩,
    ⟨[275, 9], [275], [
      .prior 716 false [],
      .prior 715 true [9],
      .equation 3 false false
        [273]
        [8, 0],
      .equation 1 true false
        [273, 8]
        [0],
      .prior 713 false [0],
      .equation 2 true false
        [273, 0]
        [],
      .equation 173 true false
        []
        [],
      .prior 717 false []]⟩,
    ⟨[277, 11], [275], [
      .equation 174 false false
        []
        [11],
      .equation 8 false false
        [275]
        []]⟩,
    ⟨[275, 11], [277], [
      .equation 174 true false
        []
        []]⟩,
    ⟨[277], [277], [
]⟩,
    ⟨[279, 13], [277], [
      .equation 175 false false
        []
        [13],
      .equation 10 false false
        [277]
        []]⟩,
    ⟨[279, 9], [279, 9], [
]⟩,
    ⟨[279], [279], [
]⟩,
    ⟨[279, 9], [279], [
      .prior 723 false [],
      .equation 175 false false
        []
        [9],
      .equation 11 false false
        [277, 8]
        [12],
      .equation 1 true false
        [277, 8]
        [12],
      .prior 720 true [9, 12],
      .equation 9 false false
        [275, 8]
        [10, 12],
      .equation 1 true false
        [275, 8]
        [10, 12],
      .prior 718 false [10, 12],
      .equation 8 true false
        [275, 10]
        [12],
      .equation 174 true false
        []
        [12],
      .prior 721 false [12],
      .equation 10 true false
        [277, 12]
        [],
      .equation 175 true false
        []
        [],
      .prior 724 false []]⟩,
    ⟨[281, 1], [279], [
      .equation 176 false false
        []
        [1],
      .equation 2 false false
        [279]
        []]⟩,
    ⟨[279, 1], [281], [
      .equation 176 true false
        []
        []]⟩,
    ⟨[281, 9], [281, 9], [
]⟩,
    ⟨[281], [281], [
]⟩,
    ⟨[281, 9], [281], [
      .prior 728 false [],
      .prior 727 true [9],
      .equation 3 false false
        [279]
        [8, 0],
      .equation 1 true false
        [279, 8]
        [0],
      .prior 725 false [0],
      .equation 2 true false
        [279, 0]
        [],
      .equation 176 true false
        []
        [],
      .prior 729 false []]⟩,
    ⟨[283, 15], [281], [
      .equation 177 false false
        []
        [15],
      .equation 12 false false
        [281]
        []]⟩,
    ⟨[281, 15], [283], [
      .equation 177 true false
        []
        []]⟩,
    ⟨[283], [283], [
]⟩,
    ⟨[285, 17], [283], [
      .equation 178 false false
        []
        [17],
      .equation 14 false false
        [283]
        []]⟩,
    ⟨[285, 9], [285, 9], [
]⟩,
    ⟨[285], [285], [
]⟩,
    ⟨[285, 9], [285], [
      .prior 735 false [],
      .equation 178 false false
        []
        [9],
      .equation 15 false false
        [283, 8]
        [16],
      .equation 1 true false
        [283, 8]
        [16],
      .prior 732 true [9, 16],
      .equation 13 false false
        [281, 8]
        [14, 16],
      .equation 1 true false
        [281, 8]
        [14, 16],
      .prior 730 false [14, 16],
      .equation 12 true false
        [281, 14]
        [16],
      .equation 177 true false
        []
        [16],
      .prior 733 false [16],
      .equation 14 true false
        [283, 16]
        [],
      .equation 178 true false
        []
        [],
      .prior 736 false []]⟩,
    ⟨[287, 1], [285], [
      .equation 179 false false
        []
        [1],
      .equation 2 false false
        [285]
        []]⟩,
    ⟨[285, 1], [287], [
      .equation 179 true false
        []
        []]⟩,
    ⟨[287], [287], [
]⟩,
    ⟨[289, 3], [287], [
      .equation 180 false false
        []
        [3],
      .equation 4 false false
        [287]
        []]⟩,
    ⟨[289], [289], [
]⟩,
    ⟨[291, 5], [289], [
      .equation 181 false false
        []
        [5],
      .equation 6 false false
        [289]
        []]⟩,
    ⟨[289, 8, 4], [291], [
      .equation 1 true false
        [289, 8]
        [4],
      .equation 180 false false
        []
        [9, 4],
      .equation 5 false false
        [287]
        [8, 2, 4],
      .equation 1 true false
        [287, 8]
        [2, 4],
      .prior 739 true [9, 2, 4],
      .equation 3 false false
        [285]
        [8, 0, 2, 4],
      .equation 1 true false
        [285, 8]
        [0, 2, 4],
      .prior 737 false [0, 2, 4],
      .equation 2 true false
        [285, 0]
        [2, 4],
      .equation 179 true false
        []
        [2, 4],
      .prior 740 false [2, 4],
      .equation 4 true false
        [287, 2]
        [4],
      .equation 180 true false
        []
        [4],
      .prior 742 false [4],
      .equation 6 true false
        [289, 4]
        [],
      .equation 181 true false
        []
        []]⟩,
    ⟨[291, 9], [291, 9], [
]⟩,
    ⟨[291], [291], [
]⟩,
    ⟨[291, 9], [291], [
      .prior 745 false [],
      .equation 181 false false
        []
        [9],
      .equation 7 false false
        [289]
        [8, 4],
      .prior 744 false [],
      .prior 746 false []]⟩,
    ⟨[293, 1], [291], [
      .equation 182 false false
        []
        [1],
      .equation 2 false false
        [291]
        []]⟩,
    ⟨[291, 1], [293], [
      .equation 182 true false
        []
        []]⟩,
    ⟨[293, 9], [293, 9], [
]⟩,
    ⟨[293], [293], [
]⟩,
    ⟨[293, 9], [293], [
      .prior 750 false [],
      .prior 749 true [9],
      .equation 3 false false
        [291]
        [8, 0],
      .equation 1 true false
        [291, 8]
        [0],
      .prior 747 false [0],
      .equation 2 true false
        [291, 0]
        [],
      .equation 182 true false
        []
        [],
      .prior 751 false []]⟩,
    ⟨[295, 11], [293], [
      .equation 183 false false
        []
        [11],
      .equation 8 false false
        [293]
        []]⟩,
    ⟨[293, 11], [295], [
      .equation 183 true false
        []
        []]⟩,
    ⟨[295, 9], [295, 9], [
]⟩,
    ⟨[295], [295], [
]⟩,
    ⟨[295, 9], [295], [
      .prior 755 false [],
      .prior 754 true [9],
      .equation 9 false false
        [293, 8]
        [10],
      .equation 1 true false
        [293, 8]
        [10],
      .prior 752 false [10],
      .equation 8 true false
        [293, 10]
        [],
      .equation 183 true false
        []
        [],
      .prior 756 false []]⟩,
    ⟨[297, 13], [295], [
      .equation 184 false false
        []
        [13],
      .equation 10 false false
        [295]
        []]⟩,
    ⟨[295, 13], [297], [
      .equation 184 true false
        []
        []]⟩,
    ⟨[297, 9], [297, 9], [
]⟩,
    ⟨[297], [297], [
]⟩,
    ⟨[297, 9], [297], [
      .prior 760 false [],
      .prior 759 true [9],
      .equation 11 false false
        [295, 8]
        [12],
      .equation 1 true false
        [295, 8]
        [12],
      .prior 757 false [12],
      .equation 10 true false
        [295, 12]
        [],
      .equation 184 true false
        []
        [],
      .prior 761 false []]⟩,
    ⟨[299, 1], [297], [
      .equation 185 false false
        []
        [1],
      .equation 2 false false
        [297]
        []]⟩,
    ⟨[297, 1], [299], [
      .equation 185 true false
        []
        []]⟩,
    ⟨[299, 9], [299, 9], [
]⟩,
    ⟨[299], [299], [
]⟩,
    ⟨[299, 9], [299], [
      .prior 765 false [],
      .prior 764 true [9],
      .equation 3 false false
        [297]
        [8, 0],
      .equation 1 true false
        [297, 8]
        [0],
      .prior 762 false [0],
      .equation 2 true false
        [297, 0]
        [],
      .equation 185 true false
        []
        [],
      .prior 766 false []]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
