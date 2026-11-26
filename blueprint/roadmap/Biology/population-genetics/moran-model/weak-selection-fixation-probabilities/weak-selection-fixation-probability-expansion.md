# First-order weak-selection expansion of fixation probability

In the replacement process of [the setup](reproductive-value-and-neutral-fixation.md), with reproductive values
$\pi_1, \dots, \pi_N$ and $\hat x = \sum_i \pi_i x_i$, let

$$\widehat\Delta_{\mathrm{sel}}(x) = \mathbb{E}_\delta[\hat x' - \hat x \mid x] = \sum_{i=1}^N \pi_i \sum_{j=1}^N e_{ji}(x)\,(x_j - x_i)$$

be the expected one-step change in reproductive-value-weighted allele frequency from state $x$ at selection
intensity $\delta$. It vanishes at $\mathbf{A}$ and $\mathbf{B}$ and, by neutrality, for every $x$ at $\delta = 0$.
Then for every transient initial state $\xi \in \mathbb{B}_T^N$, the fixation probability $\rho_A(\xi)$ of
$A$ at selection intensity $\delta$ satisfies

$$\rho_A(\xi) = \hat\xi + \delta \left\langle \left.\frac{d}{d\delta} \widehat\Delta_{\mathrm{sel}}\right|_{\delta=0} \right\rangle_\xi^\circ + O(\delta^2) \qquad (\delta \to 0),$$

where $\langle \cdot \rangle_\xi^\circ$ is the [neutral sojourn-time operator](sojourn-times-as-rare-mutation-derivative.md)
from $\xi$.

## Depends on

- [Reproductive values and neutral fixation probability](reproductive-value-and-neutral-fixation.md)
- [Sojourn times as the rare-mutation derivative of the stationary distribution](sojourn-times-as-rare-mutation-derivative.md)

## Expansion

Since $\hat x(t)$ is bounded and absorbed at $\hat{\mathbf{A}} = 1$ or $\hat{\mathbf{B}} = 0$,
$\rho_A(\xi) = \lim_t \mathbb{E}[\hat x(t)] = \hat\xi + \sum_{t \ge 0} \mathbb{E}[\widehat\Delta_{\mathrm{sel}}(x_t)]$,
which is the exact identity $\rho_A(\xi) = \hat\xi + \langle \widehat\Delta_{\mathrm{sel}} \rangle_\xi$ at
intensity $\delta$. The transition probabilities, hence the sojourn times $t_\xi(x)$, are smooth in $\delta$ near
$0$, and $\widehat\Delta_{\mathrm{sel}} \equiv 0$ at $\delta = 0$, so differentiating
$\sum_{x \in \mathbb{B}_T^N} \widehat\Delta_{\mathrm{sel}}(x)\, t_\xi(x)$ at $\delta = 0$ leaves only the
derivative of $\widehat\Delta_{\mathrm{sel}}$ against the neutral sojourn times, and Taylor's theorem gives the
$O(\delta^2)$ remainder.

## Sources

- A. McAvoy and B. Allen, "Fixation probabilities in evolutionary dynamics under weak selection", Journal of Mathematical Biology 82 (2021), 14, <https://doi.org/10.1007/s00285-021-01568-4>. (Theorem 1 and Eq. 13.)
