# Evolutionary stability of ideal free natal dispersal

**Competition model.** Two ecologically identical species with densities $u_i, v_i$ differ only in their natal dispersal matrices $(d_{ij})$ and $(D_{ij})$:

$$
\Delta u_i = s_i(u_i + v_i) \sum_j d_{ij} f_j(u_j + v_j) u_j - m_i(u_i + v_i) u_i, \qquad \Delta v_i = s_i(u_i + v_i) \sum_j D_{ij} f_j(u_j + v_j) v_j - m_i(u_i + v_i) v_i,
$$

under the assumptions of [Source–sink dichotomy for natal dispersal models](source-sink-dichotomy-for-natal-dispersal-models.md). When all patches are sources ($g_i(0) > 1$) with carrying capacities $u_i^*$, $(d_{ij})$ is an *ideal free dispersal strategy* if $\sum_j d_{ij} f_j(u_j^*) u_j^* = f_i(u_i^*) u_i^*$ for all $i$.

**Key inequality.** A nonnegative $n \times n$ matrix $A$ is line-sum-symmetric (each row sum equals the corresponding column sum) iff

$$
\sum_{i,j} a_{ij} \frac{x_i}{x_j} \ge \sum_{i,j} a_{ij} \quad \text{for all } x_1, \dots, x_n > 0,
$$

and for irreducible line-sum-symmetric $A$ equality holds iff all $x_i$ coincide.

**Theorem.** Assume (A1)–(A4), $(D_{ij})$ satisfies (A1), and $g_i(0) > 1$ for all $i$.

1. If $(d_{ij})$ is ideal free and $(D_{ij})$ is not, then $(u^*, 0)$ is globally asymptotically stable among nonnegative, not identically zero initial data: the ideal free strategy excludes every other strategy, and cannot be invaded.
2. If both are ideal free, the nonnegative equilibria are $(0,0)$ and the segment $\{(\alpha u^*, (1-\alpha) u^*) : 0 \le \alpha \le 1\}$; under a mild differentiability and monotonicity condition ($f_i' + s_i' - m_i' < 0$, plus a discrete-time analogue), every positive solution converges to a point of this segment.
3. *(Sinks.)* If patches $1, \dots, k$ ($k < n$) are sources and the others sinks, with some $g_i(0) < 1$, $i > k$, set $u_i^* > 0$ with $g_i(u_i^*) = 1$ for $i \le k$ and $u_i^* = 0$ for $i > k$. A sedentary resident (no dispersal, $\Delta u_i = s_i f_i u_i - m_i u_i$ with total density as argument) competing against any species with dispersal matrix $(D_{ij})$ satisfying (A1) wins: $(u^*, 0)$ is globally asymptotically stable among positive initial data, because irreducible dispersal necessarily loses offspring to sinks. The corresponding statement for an ideal free resident is stated as a conjecture.

## Depends on

- [Source–sink dichotomy for natal dispersal models](source-sink-dichotomy-for-natal-dispersal-models.md)

## Expansion

At $(u^*, 0)$ the line-sum-symmetric inequality, applied to the offspring-flow matrix of the ideal free resident with weights given by the invader's profile, shows that an invader with a different strategy has negative growth rate when rare and that the resident cannot be displaced. Global stability then uses the monotone (competitive) structure of the two-species system ensured by (A3). Because dispersal and demography enter multiplicatively (dispersal acts on newborns), these results require new methods compared with models of lifelong (breeding) dispersal, where they enter additively.

## Sources

- R. S. Cantrell, C. Cosner, Y. Lou, S. J. Schreiber, "Evolution of natal dispersal in spatially heterogenous environments", arXiv:1608.08314 (2016): Definition 3.1 (ideal free dispersal strategy), Theorem 2 (line-sum-symmetric matrices), Theorems 3 and 4 (evolutionary stability and neutrality of ideal free strategies), Section 3.2 (Theorem 5 and Conjecture 1, sedentary residents in source–sink landscapes). <https://doi.org/10.48550/arXiv.1608.08314> Published version: Mathematical biosciences 283 (2017): 136-144, <https://doi.org/10.1016/j.mbs.2016.11.003>.
