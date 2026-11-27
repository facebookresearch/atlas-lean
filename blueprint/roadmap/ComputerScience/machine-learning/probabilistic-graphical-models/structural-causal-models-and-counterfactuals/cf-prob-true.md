# Without evidence, counterfactuals are interventions

Let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in a
finite nonempty set $\alpha$ and disturbances in a finite set. For a finite set $W$ of nodes,
$w \in \alpha^n$ and an event $Y \subseteq \alpha^n$, the
[counterfactual probability](cf-prob.md) of $Y$ under $\mathrm{do}(X_W = w)$ given the certain
event is the probability of $Y$ under the law of the [submodel](do-set.md) of
$\mathrm{do}(X_W = w)$: $P(X_{W \leftarrow w} \in Y) = P(Y \mid \mathrm{do}(X_W = w))$.
