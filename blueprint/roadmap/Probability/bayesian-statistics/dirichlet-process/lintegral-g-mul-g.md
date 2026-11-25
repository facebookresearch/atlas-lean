# Mixed second moment of the random measure

For a [stick-breaking process](stick-breaking-process.md) on a probability space $(\Omega, \mu)$ with base measure $H$, if $\sum_{k \ge 0} \pi_k = 1$ almost surely, then for all measurable $A, B \subseteq X$,

$$\mathbb{E}[G(A)\, G(B)] = (1 - s)\, H(A)\, H(B) + s\, H(A \cap B),$$

where $s = \sum_k \mathbb{E}[\pi_k^2] \le 1$ is the [expected sum of squared weights](sum-sq-weight.md): two draws from $G$ pick the same piece with probability $s$, and otherwise land on two independent atoms.
