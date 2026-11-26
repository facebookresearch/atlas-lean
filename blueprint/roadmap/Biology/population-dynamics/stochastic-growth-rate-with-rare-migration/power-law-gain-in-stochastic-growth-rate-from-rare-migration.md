# Power-law gain in the stochastic growth rate from rare migration

**Model.** A population occupies $d$ sites. In period $t$ the local growth factors form an i.i.d. sequence of diagonal matrices $D_t = \operatorname{diag}(\xi_t^{(0)}, \dots, \xi_t^{(d-1)})$ (environmental stochasticity), with log growth rates $X_t^{(i)} = \log \xi_t^{(i)}$ of mean $\mu_i$; site $0$ has the strictly largest mean, and $\tilde\mu^{(j)} = \mu_0 - \mu_j > 0$. Assume $X_t^{(0)}$ is Gaussian and each difference $X_t^{(j)} - X_t^{(0)}$ is Gaussian with mean $-\tilde\mu^{(j)}$ and variance $\tau^{(j)}$ (sub-Gaussian tails suffice, with modified constants). Migration is given by i.i.d. nonnegative matrices $A_t$ with zero diagonal, bounded above, supported on an irreducible directed migration graph $\mathcal{M}$, with $\mathbb{E}[A_t(j,i) \mid D_t]$ bounded below on its edges; a bounded diagonal penalty $\Delta_t$ acts multiplicatively. For migration intensity $\epsilon > 0$,

$$ D_t(\epsilon) = e^{\epsilon \Delta_t} D_t + \epsilon A_t, \qquad a(\epsilon) = \lim_{T \to \infty} \frac{1}{T} \log \bigl( D_T(\epsilon) \cdots D_1(\epsilon) \bigr)_{ij}, $$

the stochastic growth rate (almost surely constant and independent of $i, j$), with $a(0) = \mu_0$.

For each $j \ge 1$ let $\kappa_j \ge 2$ be the length of the shortest cycle in $\mathcal{M}$ from $0$ through $j$ back to $0$, and $\rho^{(j)} = \tilde\mu^{(j)} / \tau^{(j)}$.

**Theorem 1.** Let $j$ minimize $\kappa_j \rho^{(j)}$ and $j'$ minimize $\kappa_{j'} \rho^{(j')} / (1 + 2\rho^{(j')})$. If the penalty at the best site vanishes ($\Delta^0 = 0$), then for every $c > 0$ there are constants $C, C' > 0$ such that for all sufficiently small $\epsilon > 0$,

$$ \frac{C}{\log \epsilon^{-1}}\, \epsilon^{2 \kappa_j \rho^{(j)}} \le a(\epsilon) - a(0) \le C' \bigl( \epsilon \log \epsilon^{-1} \bigr)^{2 \kappa_{j'} \rho^{(j')} / (1 + 2 \rho^{(j')})} (\log \epsilon^{-1})^{c}. $$

If instead $\mathbb{E}[\Delta^0] < 0$ (migration costs survival at the best site): both bounds still hold when $2 \kappa_j \rho^{(j)} < 1$; the upper bound holds when $\frac{2 \kappa_{j'} \rho^{(j')}}{1 + 2\rho^{(j')}} < 1 \le 2 \kappa_j \rho^{(j)}$; and when $\frac{2 \kappa_{j'} \rho^{(j')}}{1 + 2\rho^{(j')}} > 1$, $a$ is differentiable at $0$ with $a'(0) = -\Delta^0$.

For two sites ($\kappa = 2$) the gain lies between $\epsilon^{4\tilde\mu/\tau}$ and roughly $\epsilon^{4\tilde\mu/(2\tilde\mu + \tau)}$. Since these exponents can be below $1$, a small amount of migration raises the long-run growth rate faster than any linear cost: when the mean log-growth advantage of the best site is small relative to the variance of the difference, migration is favored by selection even if it carries a penalty.

## Expansion

Expanding the product $R_T(\epsilon)$ entrywise expresses $\log R_T(0,0)$ as $\sum_t X_t^{(0)}$ plus the log of one plus a sum over excursion sequences, each excursion leaving site $0$ along a cycle of $\mathcal{M}$ and costing a factor $\epsilon^{\kappa}$ (Lemma 2). An excursion of length $s$ through site $j$ pays off when the random walk $\sum (X_t^{(j)} - X_t^{(0)})$, with drift $-\tilde\mu^{(j)}$ and variance $\tau^{(j)}$ per step, stays high; heuristically, by Gaussian large deviations, runs where site $j$ outperforms site $0$ by a margin occur with probability about $e^{-s (\tilde\mu^{(j)})^2 / (2\tau^{(j)})}$. Balancing the $\epsilon^{\kappa_j}$ cost against the gain in such runs yields the lower bound by exhibiting a positive density of profitable excursions, and the upper bound by controlling all excursion sequences with sub-Gaussian (Orlicz norm) tail estimates. A penalty at site $0$ subtracts about $\epsilon\, \mathbb{E}[\Delta^0]$, which dominates exactly when the excursion gain is $o(\epsilon)$.

## Sources

- David Steinsaltz, Shripad Tuljapurkar, "Stochastic growth rates for populations in random environments with rare migration", arXiv (2018). Section 1 (assumptions, definitions of $\kappa_j$ and $\rho^{(j)}$), Theorem 1, Lemma 2, and the sub-Gaussian extension. <https://doi.org/10.48550/arXiv.1809.04025>
