# Oco lower bound

Main lower bound: every deterministic online algorithm on
`[-D / 2, D / 2]` suffers regret at least
`(D * G / 2) * √(T / 3)` against some sign sequence. The comparator term is
already evaluated inside `regret`, with `comparator_lower_bound` and
`comparator_attained` justifying that evaluated form; by averaging,
`online_play_expectation_zero` kills the play term, so mean regret is
`(D * G / 2)` times the mean absolute sign sum, bounded below by
`khintchine_lower`; some sequence attains at least the mean
(`Finset.exists_le_of_sum_le`).
