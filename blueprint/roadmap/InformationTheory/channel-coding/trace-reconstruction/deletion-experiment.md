# Binary deletion experiment and trace sample budgets

For a word of length $n$ and real $0\le q\le1$, a trace is the increasing-order list of symbols at indices retained by independent Bernoulli masks with retention probability $1-q$. The law is the pushforward of the finite product mask law to lists; deleted positions are not supplied. An $m$-trace experiment uses the product of $m$ copies of this law for the same hidden word. A randomized estimator is a probability law on length-$n$ guesses for each list tuple and succeeds by exact equality with the hidden word. The sample-budget functional at $s$ is the infimum in the extended nonnegative reals of natural budgets cast into that type admitting one estimator whose probability is at least $s$ for every word. An empty admissible set gives infinity.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TraceReconstruction.lean#L10-L57)
