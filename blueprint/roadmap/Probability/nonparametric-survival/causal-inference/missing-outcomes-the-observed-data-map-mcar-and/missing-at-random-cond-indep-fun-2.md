# Missing At Random Cond Indep Fun

Let $\Omega$ be a standard Borel space, $\mu$ a finite measure on it, $R \subseteq \Omega$ a measurable response event, $X : \Omega \to \mathcal X$ measurable with $\mathcal X$ countable with measurable singletons, and $Y : \Omega \to \mathcal Y$ measurable with $\mathcal Y$ a measurable space. If the outcome is missing completely at random ($\mathbf 1_R$ independent of $(X, Y)$ under $\mu$), then it is missing at random: $\mathbf 1_R$ is conditionally independent of $Y$ given $\sigma(X)$, that is, for all measurable $A \subseteq \{0,1\}$ and $B \subseteq \mathcal Y$,

$$\mu\bigl(\{\mathbf 1_R \in A\} \cap \{Y \in B\} \mid \sigma(X)\bigr) = \mu(\mathbf 1_R \in A \mid \sigma(X))\, \mu(Y \in B \mid \sigma(X)) \quad \mu\text{-a.e.}$$
