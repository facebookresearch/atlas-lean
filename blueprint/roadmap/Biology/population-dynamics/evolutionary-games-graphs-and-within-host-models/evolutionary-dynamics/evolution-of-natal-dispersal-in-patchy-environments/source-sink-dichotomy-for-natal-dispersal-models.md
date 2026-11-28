# Source–sink dichotomy for natal dispersal models

**Model.** $n$ patches with densities (or occupancy frequencies) $u_i \in \mathbb{S}$, where $\mathbb{S} = \mathbb{R}_+$ for density models and $[0,1]$ for patch-occupancy (metapopulation) models. Individuals disperse only right after birth (natal dispersal):

$$
\Delta u_i = s_i(u_i) \sum_{j=1}^n d_{ij} f_j(u_j) u_j - m_i(u_i) u_i, \qquad 1 \le i \le n,
$$

with $\Delta u_i = du_i/dt$ in continuous time and $\Delta u_i = u_i(t+1) - u_i(t)$ in discrete time. Here $f_j$ is fecundity, $d_{ij}$ the fraction of offspring from patch $j$ that settle in patch $i$, $s_i$ settlement survival and $m_i$ mortality. Assumptions: (A1) $(d_{ij})$ is nonnegative, column stochastic, and irreducible (continuous time) or primitive (discrete time); (A2) $f_i, s_i$ are continuous, positive, non-increasing and $m_i$ is continuous, positive, non-decreasing; (A3) $u_i f_i(u_i)$ is strictly increasing (in discrete time, the stronger condition $\partial_{u_i}[s_i d_{ii} f_i + (1 - m_i) u_i] > 0$); (A4) the patch fitness

$$
g_i(u_i) = \frac{s_i(u_i) f_i(u_i)}{m_i(u_i)}
$$

(lifetime number of surviving offspring of a non-disperser at fixed density $u_i$) is strictly decreasing with $g_i < 1$ at high density. Patch $i$ is a *source* if $g_i(0) > 1$ and a *sink* if $g_i(0) \le 1$.

**Theorem (dichotomy).** Under (A1)–(A4), at any positive equilibrium $u^*$ either

1. $g_i(u_i^*) = 1$ in every patch (every individual exactly replaces itself), or
2. there are patches $i, j$ with $g_i(u_i^*) < 1$ and $g_j(u_j^*) > 1$ (some patches act as local sources and others as local sinks at equilibrium).

When all patches are sources and $u_i^*$ denotes the carrying capacity ($g_i(u_i^*) = 1$), the ideal free distribution $u^*$ is an equilibrium iff the *ideal free* balance condition $\sum_j d_{ij} f_j(u_j^*) u_j^* = f_i(u_i^*) u_i^*$ holds for every $i$, i.e. each patch receives as many offspring as it produces.

## Expansion

At equilibrium, dividing patch $i$'s equation by $m_i(u_i^*) u_i^*$ gives $\sum_j d_{ij} f_j u_j^* = f_i u_i^* / g_i(u_i^*)$. Summing over $i$ and using column-stochasticity, total offspring produced equals total offspring settled, so $\sum_i f_i u_i^* (1/g_i(u_i^*) - 1) = 0$; hence either every $g_i = 1$ or the $g_i - 1$ take both signs. The Mouquet–Loreau metapopulation model, $\dot u_i = (1 - u_i) \sum_j d_{ij} b_j u_j - m_i u_i$, is the case $s_i = 1 - u_i$, $f_i = b_i$, $g_i = b_i(1 - u_i)/m_i$.

## Sources

- R. S. Cantrell, C. Cosner, Y. Lou, S. J. Schreiber, "Evolution of natal dispersal in spatially heterogenous environments", arXiv:1608.08314 (2016): Section 2 (model, assumptions (A1)–(A4), patch fitness $g_i$, Mouquet–Loreau example, Theorem 1, the lemma characterizing $u^*$ as an equilibrium by the ideal free condition). <https://doi.org/10.48550/arXiv.1608.08314> Published version: Mathematical biosciences 283 (2017): 136-144, <https://doi.org/10.1016/j.mbs.2016.11.003>.
