# The Blackwell–MacQueen urn for two draws

For a [Dirichlet process](is-dirichlet.md) with concentration $\alpha$ and base measure $H$ given by a stick-breaking process on a probability space, and all measurable $A, B$,

$$\mathbb{E}[G(A)\, G(B)] = \int_A Q_x(B)\, H(dx), \qquad Q_x = \frac{\alpha H + \delta_x}{\alpha + 1},$$

where $Q_x$ is the [predictive law](polya-urn-predictive.md) after one observation $x$. If $X_1, X_2$ are i.i.d. draws from $G$, the left side is $\mathbb{P}(X_1 \in A, X_2 \in B)$, so the predictive law of $X_2$ given $X_1 = x$ is $Q_x$.

## Sources

- David Blackwell and James B. MacQueen, *Ferguson distributions via Pólya urn schemes*, Ann. Statist. 1 (1973), no. 2, 353–355, DOI 10.1214/aos/1176342372.
