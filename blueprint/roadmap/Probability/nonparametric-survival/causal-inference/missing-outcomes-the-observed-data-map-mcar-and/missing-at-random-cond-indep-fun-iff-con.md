# MAR on the common domain

Let $\Omega$ be a standard Borel space, $\mu$ a finite measure on it, $R \subseteq \Omega$ a measurable response event, $X : \Omega \to \mathcal X$ measurable with $\mathcal X$ countable with measurable singletons, and $Y : \Omega \to \mathcal Y$ measurable with $\mathcal Y$ a measurable space. Then the outcome is missing at random, meaning $\mathbf 1_R$ is conditionally independent of $Y$ given $\sigma(X)$ under $\mu$, if and only if $R$ is conditionally independent of $Y$ given $X$ in the discrete sense: for every measurable $B \subseteq \mathcal Y$ and every $x \in \mathcal X$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$
