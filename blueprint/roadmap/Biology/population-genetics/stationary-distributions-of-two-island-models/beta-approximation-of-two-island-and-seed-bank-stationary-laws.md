# Beta and two-island diffusion approximations of stationary laws of two-island and seed-bank models

**Two-island Wright–Fisher model.** Two haploid islands of sizes $N$ and $M$ carry types $1$ and $2$; $(X,Y)$ are the type-$1$ fractions. Each generation, on island $1$, $N-c$ offspring pick parents from island $1$ and $c$ from island $2$; on island $2$, $M-c$ pick parents from island $2$ and $c$ from island $1$ ($1 \le c \le \min\{N,M\}$). Offspring of island-$1$ parents mutate $2\to1$ with probability $p_1$ and $1\to2$ with probability $p_2$; offspring of island-$2$ parents use $q_1, q_2$. **Seed-bank model.** Same, except the second population (the seed bank, size $M$) does not reproduce or mutate: $c$ dormant individuals sampled without replacement re-enter the active population, the other $M-c$ persist, and $c$ new seeds are sampled from the active population.

Assume weak mutation ($p_i = \hat p_i/N$, $q_i = \hat q_i/N$), $M = mN$, and migration $c = \hat c N^\varepsilon$ with $\varepsilon \in [0,1]$.

**Theorem.** Let $(X,Y)$ have the stationary law of the finite chain.
1. *(Strong migration: beta limit.)* For $h \in C^{2,1}[0,1]$, with $Z \sim \mathrm{Beta}(a_1,a_2)$,

$$\Big|\mathbb E\,h\Big(\tfrac{N}{N+M}X + \tfrac{M}{N+M}Y\Big) - \mathbb E\,h(Z)\Big| = O\big(N^{-\varepsilon/2}\big),$$

where $a_1 = 2(Np_1 + Mq_1)$, $a_2 = 2(Np_2 + Mq_2)$ for the two-island model and $a_i = 2(N+M)p_i$ for the seed-bank model.
2. *(Weak migration: two-island diffusion limit.)* For monomials $h(x,y) = x^ny^m$, $|\mathbb E\,h(X,Y) - \mathbb E\,h(Z_1,Z_2)| = O\big(N^{\max\{2\varepsilon - 1, -1/2\}}\big)$, where $(Z_1,Z_2)$ has the stationary law of the two-island (respectively seed-bank) Wright–Fisher diffusion with mutation and migration parameters matched to $(p_i, q_i, c)$.

In the seed-bank model, $\mathbb E(X - Y)^2 = \dfrac{m\hat p_1\hat p_2}{\hat c(\hat p_1 + \hat p_2)\big(1 + 2(m+1)(\hat p_1 + \hat p_2)\big)}N^{-\varepsilon} + o(N^{-\varepsilon})$, which quantifies how strong migration homogenizes the two populations.

## Expansion

Both bounds come from Stein's method: the generator of the finite chain is compared with the generator of the limit (a one-dimensional Wright–Fisher diffusion with mutation, whose stationary law is Beta, or a two-dimensional diffusion with linear migration drift), and bounds on derivatives of the Stein solution turn the generator discrepancy into a distance between stationary laws. When migration dominates mutation the islands mix faster than mutation acts, so only the size-weighted average carries information and it behaves like a single panmictic population of size $N+M$; when migration is of the order of mutation, each island keeps its own frequency and the two-island diffusion is the right approximation.

## Sources

- H. L. Gan, M. Wilke-Berenguer, "Stationary distribution approximations of two-island Wright-Fisher and seed-bank models using Stein's method", arXiv:2405.18763 (2024), Theorems 2.1, 2.2, 3.2 and 3.4, <https://doi.org/10.48550/arXiv.2405.18763>.
