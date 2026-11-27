# Output moments of const input

Let $(\Omega, \mu)$ be a probability space, let $\iota$ and $\kappa$ be finite index sets, $H \in \mathbb{R}^{\iota \times \kappa}$, $R \in \mathbb{R}^{\iota \times \iota}$ positive semidefinite, and $Z : \Omega \to \mathbb{R}^\iota$ measurable with $Z \sim \mathcal{N}(0, R)$. For a deterministic input $X \equiv c$ with $c \in \mathbb{R}^\kappa$:

- the output mean is $\int (Hc + Z) \, d\mu = Hc$;
- the input covariance is zero: $\operatorname{Cov}_\mu(c_a, c_b) = 0$ for all $a, b \in \kappa$;
- the output covariance is $R$: $\operatorname{Cov}_\mu\big((Hc + Z)_i, (Hc + Z)_j\big) = R_{ij}$ for all $i, j \in \iota$.
