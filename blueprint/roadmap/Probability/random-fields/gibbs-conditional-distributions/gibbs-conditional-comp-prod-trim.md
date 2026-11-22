# Disintegration in product form for the outside conditional distribution

Let $E$ be a countable set, $\mu$ a finite measure on $\{0, 1\}^E$, $\Lambda \subseteq E$, $\mathcal{F}_{\Lambda^c}$ the [σ-algebra of the configuration outside](outside-sigma.md) $\Lambda$ and $\kappa_\Lambda$ the [conditional distribution given the outside](gibbs-conditional.md) of $\Lambda$. Then the measure $\mu|_{\mathcal{F}_{\Lambda^c}} \otimes \kappa_\Lambda$ on $\{0, 1\}^E \times \{0, 1\}^E$ (with the σ-algebra $\mathcal{F}_{\Lambda^c} \otimes \mathcal{F}$, $\mathcal{F}$ the product σ-algebra) is the image of $\mu$ under $\omega \mapsto (\omega, \omega)$:

$$\int \mathbf{1}_{A}(\omega)\, \kappa_\Lambda(\omega, B)\, \mu(d\omega) = \mu(A \cap B) \quad \text{for } A \in \mathcal{F}_{\Lambda^c},\ B \in \mathcal{F}.$$
