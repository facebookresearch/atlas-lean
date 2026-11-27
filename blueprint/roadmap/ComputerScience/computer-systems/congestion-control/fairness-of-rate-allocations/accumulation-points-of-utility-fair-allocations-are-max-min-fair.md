# Accumulation points of utility-fair allocations are max-min fair

Let $(f_m)_{m \in \mathbb R_+}$ be increasing, differentiable, strictly concave functions on $[0, \infty)$ such that $\lim_{m \to \infty} f_m'(x + \delta)/f_m'(x) = 0$ for all $x \ge 0$ and $\delta > 0$ (for example $f_m(x) = 1 - (1 + x)^{-m}$, for which the ratio is $((1 + x)/(1 + x + \delta))^{m+1}$), and let $x^m$ be the unique feasible allocation in the [network model](network-model-and-feasible-rate-allocations.md) maximizing $\sum_s f_m(x_s)$, every source using at least one link. If $x^*$ is an accumulation point of $(x^m)$, that is $x^* = \lim_n x^{m_n}$ for some sequence $m_n \to \infty$, then $x^*$ is the [max-min fair](max-min-fair-rate-allocations.md) allocation.

**Proof idea**, for 0–1 routing ($A_{l,s} \in \{0, 1\}$), the case the source proves. Otherwise some source $i$ has no bottleneck under $x^*$; moving a small $\delta$ of rate to $i$ from larger sources $\sigma(l)$ on its saturated links stays feasible near $x^{m_n}$, and changes the objective by at least $\delta f'_{m_n}(x_i^* + 2\delta)\bigl(1 - M f'_{m_n}(x_i^* + 3\delta)/f'_{m_n}(x_i^* + 2\delta)\bigr) > 0$ for large $n$, where $M$ is the number of saturated links used by source $i$, contradicting optimality. With fractional routing the same exchange works if each donor $j$ gives up the largest of the amounts $\delta A_{l,i}/A_{l,j}$ over the links $l$ assigned to it, and $M$ is replaced by a bound on the sum of these coefficients; the adjacent [bottleneck characterization](max-min-fairness-is-equivalent-to-every-source-having-a-bottleneck.md) gives the feasibility step.

## Depends on

- [Utility-fair rate allocations](utility-fair-rate-allocations.md)
- [Max-min fair rate allocations](max-min-fair-rate-allocations.md)

## Proof depends on

- [Max-min fairness is equivalent to every source having a bottleneck](max-min-fairness-is-equivalent-to-every-source-having-a-bottleneck.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.4, Definition 1.2.4 and Lemma 1.2.1 with its proof (equations (1.12)–(1.16)), given there for $A_{l,i} \in \{0, 1\}$ with the remark that the general case is similar. The source assumes concavity and argues uniqueness of $x^m$ as for Theorem 1.2.6, which uses strict concavity; this page assumes strict concavity, and replaces the source's example $1 - x^{-m}$, undefined at $0$, by $1 - (1 + x)^{-m}$.
