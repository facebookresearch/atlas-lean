# Evidence that agrees with the antecedent

Let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in a
finite set $\alpha$ and disturbances in a finite set, with law $P$. Let $W$ be a finite set of
nodes, $w \in \alpha^n$, and $E, Y \subseteq \alpha^n$ events with $P(E) > 0$. If every
assignment in $E$ agrees with $w$ on $W$, then the
[counterfactual probability](cf-prob.md) of $Y$ under $\mathrm{do}(X_W = w)$ given $E$ is the
observational conditional probability $P(Y \mid E) = P(E \cap Y) / P(E)$ (by consistency).
