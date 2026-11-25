# Marginalizing a Q-factor onto an ancestral subset

In a Bayesian network over a finite nonempty alphabet, for observed node sets $A \subseteq H$ such that no edge of the latent projection points from $H \setminus A$ into $A$, summing $Q[H]$ over the variables in $H \setminus A$ gives $Q[A]$: $\sum_{h \setminus a} Q[H](v) = Q[A](v)$ for every $v$.

## Sources

- J. Tian and J. Pearl, "On the identification of causal effects", technical report R-290-L, 2003, Lemma 3.
