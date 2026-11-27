# Stability of compartment models with content-dependent fragmentation

**Setting.** A population of compartments (cells, vesicles) is modelled as a continuous-time Markov chain. Inside each compartment, molecular counts $x\in\mathbb Z_{\ge0}^d$ evolve independently by a stochastic mass-action reaction network $\mathcal C$ with generator $\mathcal A$. Compartments also undergo: *inflow* $0\to C$ at rate $\kappa_I$, the new compartment's contents drawn from a distribution $\mu$ on $\mathbb Z_{\ge0}^d$; *exit* $C\to0$ at rate $\kappa_E$ per compartment, deleting its contents; *coagulation* $2C\to C$ at rate $\kappa_C$ per pair, contents added; and **content-dependent fragmentation** $C\to2C$ at rate $\kappa_F S_C$, proportional to the copy number $S_C$ of a designated species $S$ in the compartment, its contents split between two daughters by a distribution $\psi$. The coarse-grained state records how many compartments have each content vector. Let $\lambda=\sum_x\mu(x)\sum_jx_j$ be the mean molecular content of an inflowing compartment.

**Theorem 3.1 (non-explosivity).** If there are $w\in\mathbb R^d_{>0}$ and $c,d>0$ with $\mathcal A(w\cdot x)\le c\,(w\cdot x)+d$ for all $x$, then the compartment model is not explosive.

**Proposition 3.9 (fragmentation can cause explosion).** There is an internal network and a one-parameter family $\psi_p$ of splitting laws for which the compartment model is explosive if $p>e^{-\alpha}$ and non-explosive if $p<e^{-\alpha}$, even though the internal chemistry alone is not explosive.

**Theorem 4.1 (positive recurrence).** Suppose $\sup_x\mathcal A(w\cdot x)<\infty$ for some $w\in\mathbb R^d_{>0}$, $\lambda<\infty$, $\kappa_C>0$ and $\kappa_E>0$. Then the empty state (no compartments) is positive recurrent, every state reachable from it is positive recurrent, and every other state is transient and reaches the positive recurrent class in finite expected time.

**Propositions 4.3 and 4.4 (birth-death of $S$).** Let the internal chemistry be $0\rightleftarrows S$ with production rate $\kappa_b$ and degradation rate $\kappa_d$, and $\lambda<\infty$. If $\kappa_C>0$ and $\kappa_E>0$, or if $\kappa_E^2+\kappa_E\kappa_d>\kappa_b\kappa_F$, then the empty state is positive recurrent (with all states positive recurrent when $\kappa_I>0$ and either $\kappa_b>0$ or $\mu\ne\delta_0$). Conversely, if $(\kappa_F-\kappa_E)\kappa_b>(\kappa_E+\kappa_d)\kappa_E$, $\kappa_I>0$ and $\kappa_C=0$, all states are transient.

## Expansion

Non-explosivity is proved with the Lyapunov function $\sum_{\text{compartments}}w\cdot x+\#\text{compartments}$: fragmentation and coagulation conserve total content, exit removes it, and inflow adds at most $\lambda$ on average, so a linear growth bound for the internal chemistry carries over. Content dependence matters because fragmentation produces more compartments exactly where $S$ is abundant; if splitting tends to keep $S$ concentrated, the number of compartments can grow without bound in finite time. For recurrence, exit at rate $\kappa_E$ per compartment and coagulation at rate $\kappa_C$ per pair together outpace linear fragmentation when internal production is bounded. In the birth-death example, a tagged lineage's expected $S$-mass grows at rate $\kappa_b$ and fragments at rate proportional to $S$, giving the explicit inequalities that separate recurrence from transience.

## Sources

- D. F. Anderson, A. S. Howells, D. Rojas La Luz, "Stochastic reaction networks within interacting compartments with content-dependent fragmentation", *Bulletin of Mathematical Biology* 88(7) (2026), 106, Theorem 3.1, Proposition 3.9, Theorem 4.1, Propositions 4.3 and 4.4, <https://doi.org/10.1007/s11538-026-01659-7> (preprint arXiv:2511.10223).
