# Max Seg Score

The **maximal segment score** `Mₙ = max_{0 ≤ i ≤ j ≤ n} (S_j - S_i)` of a score list: the
largest sum of a (possibly empty) contiguous run (`sum_le_maxSegScore_of_infix`,
`exists_infix_sum_eq_maxSegScore`). Computed by a single left-to-right fold carrying the
current Lindley value and the best-so-far value, so one addition and at most two comparisons
per score (`maxSegScore_cons` recovers the first-step recursion).
