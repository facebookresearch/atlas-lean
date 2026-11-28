# Discrete MAR gives mean MAR, on any sample space

Let $\mu$ be a finite measure on a measurable space $\Omega$ (no standard Borel assumption), $R \subseteq \Omega$ measurable, $X : \Omega \to \mathcal X$ measurable with $\mathcal X$ countable with measurable singletons, and $Y : \Omega \to \mathbb R$ measurable and integrable. Suppose $R$ is conditionally independent of $Y$ given $X$ in the discrete sense: for every measurable $B \subseteq \mathbb R$ and every $x \in \mathcal X$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

Then

$$\mathbb E_\mu[\mathbf 1_R Y \mid \sigma(X)] = \mathbb E_\mu[\mathbf 1_R \mid \sigma(X)]\, \mathbb E_\mu[Y \mid \sigma(X)] \quad \mu\text{-a.e.}$$
