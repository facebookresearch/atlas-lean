# Conditional independence implies set-wise MAR

Let $\Omega$ be a standard Borel space with σ-algebra $\mathcal F$, $\mu$ a finite measure on it, $\mathcal G \subseteq \mathcal F$ a sub-σ-algebra (the always-observed covariate information), and $R \in \mathcal F$ the response event. Write $P(A \mid \mathcal G) = \mathbb E_\mu[\mathbf 1_A \mid \mathcal G]$. Let $Y : \Omega \to \mathcal Y$ be measurable, with $\mathcal Y$ a measurable space. If the response indicator $\mathbf 1_R$ is conditionally independent of $Y$ given $\mathcal G$ under $\mu$, then for every measurable $S \subseteq \mathcal Y$,

$$P(R \cap \{Y \in S\} \mid \mathcal G) = P(R \mid \mathcal G)\, P(Y \in S \mid \mathcal G) \quad \mu\text{-a.e.}$$

With $\mathcal G = \sigma(X)$ for a measurable covariate $X$, the hypothesis is the missing-at-random condition given $\sigma(X)$.
