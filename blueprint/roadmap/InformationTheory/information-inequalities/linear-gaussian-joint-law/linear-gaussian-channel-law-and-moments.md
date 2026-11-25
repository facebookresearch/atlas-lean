# Linear Gaussian channel: joint law and moments

Let $(\Omega, \mu)$ be a probability space, let $\iota$ and $\kappa$ be finite nonempty index sets, $H \in \mathbb{R}^{\iota \times \kappa}$, and $R \in \mathbb{R}^{\iota \times \iota}$ positive definite. Let $X : \Omega \to \mathbb{R}^\kappa$ and $Z : \Omega \to \mathbb{R}^\iota$ be measurable and independent, with $Z \sim \mathcal{N}(0, R)$, and suppose $X$ has finite second moment, mean $m$ and covariance matrix $K$, $K_{ab} = \operatorname{Cov}_\mu(X_a, X_b)$. Then:

- the joint law of $(X, HX + Z)$ is $X_\ast\mu \otimes N_H$, where $N_H$ sends $x$ to the law of $Hx + Z'$ with $Z' \sim \mathcal{N}(0, R)$;
- $HX + Z$ has finite second moment;
- $\int (HX + Z) \, d\mu = Hm$;
- $\operatorname{Cov}_\mu\big((HX + Z)_i, (HX + Z)_j\big) = (HKH^\top + R)_{ij}$ for all $i, j \in \iota$;
- $\operatorname{tr} K + \lVert m \rVert^2 = \int \lVert X \rVert^2 \, d\mu$.
