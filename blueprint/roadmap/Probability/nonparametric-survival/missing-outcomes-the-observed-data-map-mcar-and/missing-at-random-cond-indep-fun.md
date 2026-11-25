# Missing at random

Let $\Omega$ be a standard Borel space, $\mu$ a finite measure on it, $R \subseteq \Omega$ the response event, $X : \Omega \to \mathcal X$ a measurable always-observed covariate and $Y : \Omega \to \mathcal Y$ an outcome, with $\mathcal X, \mathcal Y$ measurable spaces. The outcome is missing at random (MAR, Rubin 1976) if the response indicator $\mathbf 1_R$ is conditionally independent of $Y$ given $\sigma(X)$ under $\mu$: for all measurable $A \subseteq \{0,1\}$ and $B \subseteq \mathcal Y$,

$$\mu\bigl(\{\mathbf 1_R \in A\} \cap \{Y \in B\} \mid \sigma(X)\bigr) = \mu\bigl(\mathbf 1_R \in A \mid \sigma(X)\bigr)\, \mu\bigl(Y \in B \mid \sigma(X)\bigr) \quad \mu\text{-a.e.}$$

For a countably valued covariate with measurable singletons and a real outcome, this agrees with the discrete-covariate form of missing at random stated through joint probabilities of the level sets $\{X = x\}$.
