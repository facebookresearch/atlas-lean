# First-order weak-selection expansion of fixation probability

Under the smooth finite-population evolutionary process with selection intensity $\delta \ge 0$ and
reproductive values $\pi_1, \dots, \pi_N$, let $\widehat\Delta_{\mathrm{sel}}(x) = \mathbb{E}[\hat x' - \hat x \mid x]$
be the expected one-step change in reproductive-value-weighted allele frequency from state $x$.
Then for any fixed initial configuration $\xi \in \mathbb{B}^N$, the fixation probability of allele $A$
satisfies the first-order weak-selection expansion

$$\rho_A(\xi) = \hat\xi + \delta \left\langle \left.\frac{d}{d\delta} \widehat\Delta_{\mathrm{sel}}\right|_{\delta=0} \right\rangle_\xi^\circ + O(\delta^2),$$

where $\langle \cdot \rangle_\xi^\circ$ is the neutral sojourn-time operator from initial state $\xi$.

## Depends on

- [Reproductive values and neutral fixation probability](reproductive-value-and-neutral-fixation.md)
- [Sojourn times as the rare-mutation derivative of the stationary distribution](sojourn-times-as-rare-mutation-derivative.md)

## Expansion

Averaging the one-step change of $\hat x$ over the stationary distribution $\pi_{(\xi)}$ of the
$u$-amended chain yields $0 = \mathbb{E}_{(\xi)}[\widehat\Delta_{\mathrm{sel}}] - u \pi_{(\xi)}(\mathbf{A})(1 - \hat\xi) + u \pi_{(\xi)}(\mathbf{B})\hat\xi$.
Differentiating at $u = 0$ and using $\lim_{u \to 0} \pi_{(\xi)}(\mathbf{A}) = \rho_A(\xi)$ gives
the exact identity $\rho_A(\xi) = \hat\xi + \langle \widehat\Delta_{\mathrm{sel}} \rangle_\xi$.
Since $\widehat\Delta_{\mathrm{sel}}^\circ \equiv 0$ under neutrality, expanding in $\delta$ at
$\delta = 0$ produces the stated first-order formula.

## Sources

- A. McAvoy and B. Allen, "Fixation probabilities in evolutionary dynamics under weak selection", Journal of Mathematical Biology 82 (2021), 14, <https://doi.org/10.1007/s00285-021-01567-5>. (Theorem 1.)
