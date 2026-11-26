# Discrete MAR gives set-wise MAR given `σ(X)`, on any sample space

Let $\mu$ be a finite measure on a measurable space $\Omega$ (no standard Borel assumption), $R \subseteq \Omega$ measurable, $X : \Omega \to \mathcal X$ measurable with $\mathcal X$ countable with measurable singletons, and $Y : \Omega \to \mathcal Y$ measurable with $\mathcal Y$ a measurable space. Suppose $R$ is conditionally independent of $Y$ given $X$ in the discrete sense: for every measurable $B \subseteq \mathcal Y$ and every $x \in \mathcal X$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

Then for every measurable $S \subseteq \mathcal Y$,

$$P(R \cap \{Y \in S\} \mid \sigma(X)) = P(R \mid \sigma(X))\, P(Y \in S \mid \sigma(X)) \quad \mu\text{-a.e.},$$

where $P(A \mid \sigma(X)) = \mathbb E_\mu[\mathbf 1_A \mid \sigma(X)]$.
