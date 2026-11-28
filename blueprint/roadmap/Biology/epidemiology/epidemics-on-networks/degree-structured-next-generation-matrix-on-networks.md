# Degree-structured next-generation matrix on networks

**Setting.** An SIR infection spreads on a static undirected contact network without short closed loops (locally tree-like). Write $[m]$ for the number of nodes of degree $m$ and $[km]$ for the number of edges joining a node of degree $k$ to a node of degree $m$. Along each edge between an infectious and a susceptible node, transmission occurs at rate $\tau$ while the infective recovers at rate $\gamma$, so infection eventually passes across the edge with probability

$$p = \frac{\tau}{\tau + \gamma}.$$

**Proposition.** During the early phase of an epidemic, the expected number of infections of degree-$k$ nodes caused by one infected node of degree $m$ is

$$K_{km} = \frac{[km]}{m\,[m]}\,(m - 1)\,p \qquad \text{(Eq. 10)},$$

and the basic reproduction number is the dominant eigenvalue

$$R_0 = \rho\big((K_{km})\big) \qquad \text{(Eq. 11)},$$

with invasion threshold $R_0 = 1$.

**Corollary (uncorrelated networks).** If degrees are uncorrelated across edges, $[km]/(m[m]) = kP(k)/\langle k \rangle$ with degree distribution $P$, $K$ has rank one and

$$R_0 = p\,\frac{\langle k^2\rangle - \langle k\rangle}{\langle k \rangle}.$$

## Expansion

A node of degree $m$ that was infected through one of its edges has $m - 1$ further edges; a fraction $[km]/(m[m])$ of the edge ends at degree-$m$ nodes lead to degree-$k$ neighbors, and each transmits with probability $p$ before recovery. In the uncorrelated case $K_{km} = a_k b_m$ with $a_k = kP(k)p/\langle k\rangle$ and $b_m = m - 1$, so $\rho(K) = \sum_k a_k b_k$. Clustering breaks the derivation because neighbors of a node share contacts; for household or triangle-based networks the source describes alternative threshold quantities such as the clique reproduction number $R_*$, which need not match the verbal definition of $R_0$. Pairwise moment-closure models without triangles reproduce the same early growth rate.

## Sources

- L. Danon, A. P. Ford, T. House, C. P. Jewell, M. J. Keeling, G. O. Roberts, J. V. Ross, M. C. Vernon, "Networks and the epidemiology of infectious disease", Interdisciplinary Perspectives on Infectious Diseases 2011 (2011) 284909, Section 4.2.1, Eqs. 10–11, <https://doi.org/10.1155/2011/284909> (PMC3062985).
