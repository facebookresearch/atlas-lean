# MAR implies mean MAR, general covariate σ-algebra

Let $\mu$ be a finite measure on a measurable space $(\Omega, \mathcal F)$, $\mathcal G \subseteq \mathcal F$ a sub-σ-algebra (the always-observed covariate information), and $R \in \mathcal F$ the response event. Write $P(A \mid \mathcal G) = \mathbb E_\mu[\mathbf 1_A \mid \mathcal G]$. Let $Y : \Omega \to \mathbb R$ be measurable and integrable, and suppose $R$ and $Y$ are conditionally independent given $\mathcal G$ in the set-wise form: for every measurable $S \subseteq \mathbb R$,

$$P(R \cap \{Y \in S\} \mid \mathcal G) = P(R \mid \mathcal G)\, P(Y \in S \mid \mathcal G) \quad \mu\text{-a.e.}$$

Then

$$\mathbb E_\mu[\mathbf 1_R Y \mid \mathcal G] = P(R \mid \mathcal G)\, \mathbb E_\mu[Y \mid \mathcal G] \quad \mu\text{-a.e.}$$
