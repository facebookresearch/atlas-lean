# Log-odds of one alignment

Assume the [linear-gap log-odds hypotheses](linear-gap-log-odds.md): a memoryless pair HMM with strictly positive, normalised transition and emission probabilities, end weight $\tau > 0$, strictly positive normalised background frequencies $q$, $0 < \eta < 1$, and per-column log-odds scores $\sigma(a, b)$ and $g$. Then for every [valid alignment](../pairwise-sequence-alignment/is-alignment.md) $A$ of $x$ and $y$,

$$\log \frac{P(x, y, A)}{B(x, y)} = s(A) + \log \frac{\tau}{\eta^2},$$

where $P(x, y, A)$ is the [joint weight](align-prob.md), $B$ the [independence-model weight](background.md) and $s(A)$ the linear-gap [alignment score](../pairwise-sequence-alignment/alignment-score.md). The term $\log(\tau / \eta^2)$ is a correction for the transitions into the end states.
