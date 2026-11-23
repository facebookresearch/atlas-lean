# Outside conditional distribution is a version of the conditional probability

Let $E$ be a countable set, $\mu$ a finite measure on $\{0, 1\}^E$, $\Lambda \subseteq E$, and let $\kappa_\Lambda$ be the [conditional distribution given the outside of](gibbs-conditional.md) $\Lambda$. For every measurable set $s \subseteq \{0, 1\}^E$,

$$\kappa_\Lambda(\omega, s) = \mu\big(s \mid \mathcal{F}_{\Lambda^c}\big)(\omega) \quad \text{for } \mu\text{-almost every } \omega,$$

where $\mathcal{F}_{\Lambda^c}$ is the [σ-algebra of the configuration outside](outside-sigma.md) $\Lambda$ and $\mu(s \mid \mathcal{F}_{\Lambda^c}) = \mathbb{E}_\mu[\mathbf{1}_s \mid \mathcal{F}_{\Lambda^c}]$.
