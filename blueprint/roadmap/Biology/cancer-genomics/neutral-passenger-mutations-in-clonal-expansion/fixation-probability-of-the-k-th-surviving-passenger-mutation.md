# Fixation probability of the k-th surviving passenger mutation

In the multi-type birth–death model of a clonal expansion (birth rate $b$, death rate $d$, $\delta = d/b \in (0,1)$, a new neutral passenger in one daughter cell with probability $u$ per division, infinitely many alleles), label the passengers whose lineages survive as $1, 2, \dots$ in order of appearance. Approximate the population sizes at which surviving passengers arise by a Poisson process of rate $u$ on $[0, M]$ with $M \to \infty$, so the $k$-th one arises at a size $z$ with the $\mathrm{Gamma}(k, u)$ density $u(zu)^{k-1}e^{-zu}/(k-1)!$.

**Fixation.** The $k$-th surviving passenger reaches frequency one exactly when the lineages of all $z$ other cells die out, which has probability $\delta^z$. Hence

$$\rho_k \approx \int_0^\infty \frac{u(zu)^{k-1}e^{-zu}}{(k-1)!}\,\delta^z\,dz = \left(\frac{u}{u-\log\delta}\right)^{k}.$$

Fixation of passenger $k$ implies fixation of passengers $1,\dots,k-1$.

**Frequency distribution.** Combining the same Gamma law with the single-mutation law $\Pr[x \le \alpha \mid z] = 1-(1-\alpha(1-\delta))^z$, the cell fraction $x_k$ of the $k$-th surviving passenger satisfies, for $0 < \alpha < 1$,

$$\Pr[x_k \le \alpha] \approx 1 - \left(1 - \frac{\log\bigl(1-(1-\delta)\alpha\bigr)}{u}\right)^{-k},$$

so $\rho_k = 1 - \lim_{\alpha\uparrow 1}\Pr[x_k \le \alpha]$, and the median fraction is $\min\bigl\{1, (1 - e^{u(1-2^{1/k})})/(1-\delta)\bigr\}$.

## Depends on

- [Eventual fraction of a passenger mutation in a birth–death expansion](eventual-fraction-of-a-passenger-mutation-in-a-birth-death-expansion.md)

## Expansion

$\int_0^\infty u^k z^{k-1} e^{-z(u-\log\delta)}\,dz/(k-1)! = u^k/(u-\log\delta)^k$ is the Gamma moment generating function evaluated at $\log\delta < 0$. The frequency law is the same integral applied to $(1-\alpha(1-\delta))^z = e^{z\log(1-\alpha(1-\delta))}$. With the exome passenger rate $u \approx 0.015$, $\rho_1 \approx 0.04$ at $\delta = 0.72$ but $\rho_1 \approx 0.6$ at $\delta = 0.99$: in slowly growing tumours several clonal passengers can be acquired during the expansion rather than being present in the founding cell.

## Sources

- I. Bozic, J. M. Gerold, M. A. Nowak, "Quantifying clonal and subclonal passenger mutations in cancer evolution", PLoS Computational Biology 12 (2016) e1004731, Results Eqs (1)–(2) and Methods Eqs (18)–(22), <https://doi.org/10.1371/journal.pcbi.1004731> (PMC4734774).
