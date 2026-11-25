# Missing at random

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event, $Y : \Omega \to \mathbb R$ the outcome and $X : \Omega \to \mathcal X$ a covariate. The outcome is missing at random (Rubin 1976), in the discrete-covariate sense, if $R$ is conditionally independent of $Y$ given $X$ through joint probabilities: for every measurable $B \subseteq \mathbb R$ and every $x \in \mathcal X$,

$$\mu(R \cap \{Y \in B\} \cap \{X = x\})\, \mu(X = x) = \mu(R \cap \{X = x\})\, \mu(\{Y \in B\} \cap \{X = x\}).$$

The condition holds vacuously when every level set $\{X = x\}$ is null (for example for an atomless $X$); it expresses conditional independence only for a covariate with countably many values.
