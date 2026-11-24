# Events under the law of a structural causal model

Let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in a
finite set $\alpha$, disturbances in a finite set $\beta$ with laws $\pi_k$, solution $X(u)$ and
law $P$. For every event $Y \subseteq \alpha^n$,
$P(Y) = \sum_{u \in \beta^n} \prod_k \pi_k(u_k) \, \mathbf{1}[X(u) \in Y]$: the probability of an
event is the mass of the disturbances whose solution lies in it.
