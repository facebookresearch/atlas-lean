# The minimum-peak rule is the unique individually rational strategy-proof onto rule

On single-peaked preferences over $[a, b]$, the minimum-peak rule (choose the smallest reported peak) is the unique strategy-proof, onto rule that is individually rational with respect to the left endpoint $a$ (no agent strictly prefers $a$ to the outcome). Symmetrically, the maximum-peak rule is the unique such rule for the right endpoint.

## Proof sketch

Write the rule in the max-min form $\max_S \min(\beta_S, \min_{i \in S} p_i)$ of the Moulin–Ching characterization, with $\beta_\emptyset = a$ and $\beta_N = b$. For a coalition $S \ne \emptyset, N$, put the peaks of $S$ at $b$ and the others at $a$; by monotonicity the outcome is $\beta_S$, and the agents with peak $a$ strictly prefer $a$ to any other point, so individual rationality forces $\beta_S = a$. With $\beta_S = a$ for every $S \ne N$ the scheme is $\max(a, \min(b, \min_i p_i)) = \min_i p_i$, the minimum-peak rule, and that rule is strategy-proof, onto and individually rational with respect to $a$.

## Depends on

- [Ordinal single-peaked preferences on an interval](ordinal-single-peaked-preferences-on-an-interval.md)

## Proof depends on

- [Moulin–Ching characterization of strategy-proof rules on single-peaked preferences](moulin-ching-characterization-of-strategy-proof-rules-on-single-peaked-preferenc.md)

## Sources

- James Schummer and Rakesh V. Vohra, "Mechanism Design without Money", Algorithmic Game Theory, Cambridge University Press, 2007.
