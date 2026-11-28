# Log-odds grow linearly under repeated haploid selection on two types

For two types, with positive fitnesses `w_1`, `w_0` and initial frequencies `p₀(1)`, `p₀(0)` that
are both positive and sum to `1`, let `p_t` be the frequency of type `1` after `t` generations of
[haploid selection](../natural-selection-fisher-s-theorem-and-the-price/select.md) with constant
fitnesses. Then
`log (p_t / (1 - p_t)) = log (p₀(1) / (1 - p₀(1))) + t log (w_1 / w_0)` for every `t`.
