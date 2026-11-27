# Missing at random through conditional independence given the covariate

Let $\Omega$ be a standard Borel space, $\mu$ a finite measure on it, $R \subseteq \Omega$ the response event, $X : \Omega \to \mathcal X$ a measurable always-observed covariate and $Y : \Omega \to \mathcal Y$ an outcome, with $\mathcal X, \mathcal Y$ measurable spaces. The outcome is missing at random (MAR, Rubin 1976) if the response indicator $\mathbf 1_R$ is conditionally independent of $Y$ given $\sigma(X)$ under $\mu$, in the kernel sense: for the conditional-expectation kernel $\kappa$ of $\mu$ given $\sigma(X)$, which exists because $\Omega$ is standard Borel, for each measurable $A \subseteq \{0,1\}$ and each measurable $B \subseteq \mathcal Y$,

$$\kappa\bigl(\omega, \{\mathbf 1_R \in A\} \cap \{Y \in B\}\bigr) = \kappa\bigl(\omega, \{\mathbf 1_R \in A\}\bigr)\, \kappa\bigl(\omega, \{Y \in B\}\bigr)$$

for almost every $\omega$ with respect to the restriction of $\mu$ to $\sigma(X)$. The exceptional null set may depend on $A$ and $B$, so this is weaker than requiring $\mathbf 1_R$ and $Y$ to be independent under $\kappa(\omega, \cdot)$ for almost every $\omega$.

When $R$ and $Y$ are measurable, this is equivalent to the conditional-event form: for all measurable $A \subseteq \{0,1\}$ and $B \subseteq \mathcal Y$,

$$\mu\bigl(\{\mathbf 1_R \in A\} \cap \{Y \in B\} \mid \sigma(X)\bigr) = \mu\bigl(\mathbf 1_R \in A \mid \sigma(X)\bigr)\, \mu\bigl(Y \in B \mid \sigma(X)\bigr) \quad \mu\text{-a.e.}$$
