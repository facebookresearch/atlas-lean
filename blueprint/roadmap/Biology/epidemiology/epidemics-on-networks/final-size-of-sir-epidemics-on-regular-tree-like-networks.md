# Final size of SIR epidemics on regular tree-like networks

**Setting.** Every individual has exactly $n$ contacts in an unclustered (locally tree-like) network. Infection passes across an edge from an infective to a susceptible with probability $p = \tau/(\tau + \gamma)$, where $\tau$ is the per-edge transmission rate and $\gamma$ the recovery rate, and edges act independently.

**Proposition (susceptibility-set argument).** In a major outbreak in a large population, the probability $S_\infty$ that a given individual escapes infection satisfies

$$S_\infty = \big(1 - p + \tilde S p\big)^{n}, \qquad \tilde S = \big(1 - p + \tilde S p\big)^{n-1} \qquad \text{(Eq. 12)},$$

where $\tilde S$ is the probability that a neighbor, reached through one edge, escapes infection from its other $n - 1$ edges; $\tilde S$ is taken as the root in $[0,1)$ of the second equation. The expected attack rate is $R_\infty = 1 - S_\infty$.

**Percolation approximation.** If $f(\phi)$ is the fraction of nodes in the giant component after removing a fraction $\phi$ of edges, then

$$R_\infty \approx f(1 - p) \qquad \text{(Eq. 13)},$$

exact for unclustered graphs (where it reproduces Eq. 12) and approximate for clustered ones; the invasion threshold is the value of $p$ at which this giant component appears in the large-network limit.

## Depends on

- [Epidemic percolation network for SIR epidemics](../epidemics-on-networks/kenah-robins-epidemic-percolation-network-exact-isomorphism-of-network.md)

## Expansion

An individual escapes infection iff, for each of its $n$ edges, either the edge does not transmit (probability $1-p$) or it transmits but the neighbor was itself never infected through its remaining $n - 1$ edges (probability $p\tilde S$). On a tree these events are independent across edges. The neighbor's escape probability satisfies the same equation with $n - 1$ edges, giving a two-step system: two generations of infection are needed to stabilize the correlation created by the edge back to the focal node. Equivalently, each realized transmitting edge is an open bond in bond percolation with occupation probability $p$, and the final size is the size of the giant cluster.

## Sources

- L. Danon, A. P. Ford, T. House, C. P. Jewell, M. J. Keeling, G. O. Roberts, J. V. Ross, M. C. Vernon, "Networks and the epidemiology of infectious disease", Interdisciplinary Perspectives on Infectious Diseases 2011 (2011) 284909, Sections 4.2.2–4.2.3, Eqs. 12–13, <https://doi.org/10.1155/2011/284909> (PMC3062985).
- O. Diekmann, M. C. M. de Jong and J. A. J. Metz, "A deterministic epidemic model taking account of repeated contacts between the same individuals", J. Appl. Probab. 35 (1998) 448–462.
