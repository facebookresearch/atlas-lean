# Major outbreak probability with households and workplaces of tunable overlap

**Network.** A population of size $n$ is split into households of size $h\ge2$ and workplaces of size $w=dh$, with $d\ge1$ an integer. Start with each workplace made up of $d$ whole households. Each individual independently becomes a *mover* with probability $\theta\in[0,1]$ or a *remainer* otherwise, and movers are reassigned uniformly at random to the vacated workplace slots. So $\theta=0$ means complete household–workplace overlap and $\theta=1$ means household members essentially never share a workplace.

**Epidemic.** On this network runs a stochastic SIR epidemic. Infectious periods are i.i.d. copies of an arbitrary random variable $I$, possibly preceded by a latent period. During its infectious period an infective makes Poisson contacts at rate $\beta_H$ with uniformly chosen household members, at rate $\beta_W$ with uniformly chosen workplace members, and at rate $\beta_G$ with uniformly chosen members of the whole population. Let $Z^{(n)}$ be the final number infected from one initial case, and $\pi_G$ the probability that the global rate is in play ($\pi_G>0$ iff global infection is present).

**Theorem.** As $n\to\infty$, $\mathbb P(Z^{(n)}>\log n)\to\rho$. When $\pi_G>0$,

$$
\rho=1-\xi,\qquad \xi=\min\{s\in[0,1]:\phi_A(\beta_G(1-s))=s\},
$$

where $A$ is the total infectious time (severity) accumulated by the local clump: the individuals infected through household and workplace contacts alone, starting from one case. $\phi_A$ is the Laplace transform of $A$, which is a $\theta:(1-\theta)$ mixture of the clump severities started from a mover and from a remainer. Moreover $\rho>0$ iff $R_*>1$, where $R_*$ is the mean of the susceptibility-set branching process ($R_*=\infty$ when the local reproduction number $R_L\ge1$, meaning local outbreaks can become infinite). When there is no global infection, $\rho>0$ iff $R_L>1$.

## Depends on

- [Epidemic percolation network for SIR epidemics](../../epidemics-on-networks/kenah-robins-epidemic-percolation-network-exact-isomorphism-of-network.md)

## Proof sketch

Early on, the epidemic looks like a branching process of local clumps. Each clump spreads through the household and workplace complexes it touches; movers link a household to a different workplace, which creates a tree of complexes. Clumps are linked by global contacts, and a clump of severity $A$ emits $\mathrm{Poisson}(\beta_GA)$ global infections. The extinction probability is then the smallest fixed point of $s\mapsto\mathbb E[e^{-\beta_GA(1-s)}]=\phi_A(\beta_G(1-s))$. The threshold $R_*$ comes from the backward (susceptibility-set) construction. This construction lets the result hold for any $\theta$, non-constant $I$, and with or without global contacts.

## Sources

- Frank Ball, Tom Britton and Peter Neal, "An epidemic model on a network with two group structures having tunable overlap", *Advances in Applied Probability* (2026), 1–43, <https://doi.org/10.1017/apr.2026.10078>. Preprint version: arXiv:2410.06696 (2024), Section 2 (network and epidemic model), Theorem 3.1, Section 5 (Eqs. for $\phi_A$ and $R_*$), <https://doi.org/10.48550/arXiv.2410.06696>.
