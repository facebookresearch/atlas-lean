# Coalescent dual representation of the non-equilibrium allele frequency spectrum

For neutral evolution or negative selection, $\gamma \le 0$, let $(A_t)$ be the dual birth–death process of the Wright–Fisher diffusion with selection parameter $-\gamma \ge 0$: from state $k$ it jumps to $k-1$ at rate $\binom{k}{2}$ and to $k+1$ at rate $-\gamma k$, started from $A_0 = \infty$ (coming down from infinity). For $\gamma = 0$ this is the block-counting process of Kingman's coalescent. Then the non-equilibrium allele frequency spectrum at time $t$ has the representation

$$ \omega_\gamma \int_0^1 f(y)\, \mathbb{P}^{*\gamma}_{1-y}(\tau_1 \le t)\, \pi_\gamma(y)\, dy = \int_0^1 \mathbb{E}^{-\gamma}_\infty\big[(1-y)^{A_t - 1}\big]\, f(y)\, \pi_0(y)\, dy , \qquad \pi_0(y) = \frac{2}{y}, $$

for every bounded $f$ with $f(0)=f(1)=0$ and $\int_0^1 y^{-1}|f(y)|\,dy<\infty$.

In the neutral case the law of $A_t$ is explicit: with $m_{[k]} = \Gamma(m+1)/\Gamma(m-k+1)$ and $m_{(k)} = \Gamma(m+k)/\Gamma(m)$, started from $A_0 = m$,

$$ \mathbb{E}^0_m(A_t) = 1 + \sum_{k=2}^{m} e^{-\binom{k}{2} t}\, (2k-1)\, \frac{m_{[k]}}{m_{(k)}} , $$

and the formulas for $A_0 = \infty$ follow by letting $m_{[k]}/m_{(k)} \to 1$.

## Depends on

- [Non-equilibrium allele frequency spectrum](non-equilibrium-allele-frequency-spectrum.md)

## Expansion

Moment duality for the Wright–Fisher diffusion with selection, $\mathbb{E}^{\gamma}_x[(1-\xi_t)^m] = \mathbb{E}^{\gamma}_m[(1-x)^{A_t}]$ for $\gamma \ge 0$, combined with the symmetry $\gamma \mapsto -\gamma$, $x \mapsto 1-x$, gives $\mathbb{E}^\gamma_{1-x}[\xi_t^m] = \mathbb{E}^{-\gamma}_m[(1-x)^{A_t}]$ for $\gamma \le 0$. Letting $m\to\infty$ turns the left side into the fixation probability by time $t$: $\mathbb{P}^\gamma_{1-y}(\tau_1 \le t) = \mathbb{E}^{-\gamma}_\infty[(1-y)^{A_t}]$. Dividing by $1-y$ and inserting into the second form of the non-equilibrium spectrum gives the representation. For $\gamma>0$ the dual has linear births and its stationary law is Poisson with mean $2\gamma$ conditioned to be positive.

## Sources

- Ingemar Kaj and Carina F. Mugal, *The non-equilibrium allele frequency spectrum in a Poisson random field framework*, Theor. Popul. Biol. 111 (2016), 51–64. <https://doi.org/10.1016/j.tpb.2016.06.003> Section 3.2 (duality representation; Kingman transition probabilities from Griffiths and Tavaré) and Corollary 1. Locators use the numbering of the preprint arXiv:1512.04925.
