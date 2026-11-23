# Upper half of the ladder sandwich

`Mₙ ≤ max_{i ≤ Nₙ} Yᵢ`. A segment `[a, b)` starts in
some excursion `k` and ends in excursion `j ≥ k`, `j ≤ Nₙ`; since the walk does not go below
its value at the start of excursion `k` inside it, and ladder values decrease, the segment
score is at most `S_b - S_{T_j} ≤ Y_j`.
