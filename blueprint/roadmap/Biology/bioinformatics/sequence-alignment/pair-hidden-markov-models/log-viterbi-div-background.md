# Log-odds Viterbi is linear-gap Needleman–Wunsch

Assume the [linear-gap log-odds hypotheses](linear-gap-log-odds.md): a memoryless pair HMM with strictly positive, normalised transition and emission probabilities, end weight $\tau > 0$, strictly positive normalised background frequencies $q$, $0 < \eta < 1$, and per-column log-odds scores $\sigma(a, b)$ and $g$. Then for all sequences $x, y$,

$$\log \frac{V(x, y)}{B(x, y)} = \mathrm{NW}(x, y) + \log \frac{\tau}{\eta^2},$$

where $V$ is the [Viterbi value](viterbi.md), $B$ the [independence-model weight](background.md) and $\mathrm{NW}$ the [Needleman–Wunsch score](../pairwise-sequence-alignment/nw-score.md) with substitution scores $\sigma$ and gap score $g$. The term $\log(\tau / \eta^2)$ is a correction for the transitions into the end states.
