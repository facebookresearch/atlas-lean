# Tie-decay network

A **tie-decay network** on $N$ nodes is a time-dependent symmetric matrix $\mathbf B(t)=(b_{ij}(t))$ of real-valued tie strengths, with $b_{ii}\equiv0$, in which each tie decays exponentially between interactions and jumps by $1$ at each interaction. If nodes $i$ and $j$ interact at times $t_1,t_2,\dots$ and $\alpha>0$ is the decay coefficient, then

$$b_{ij}(t)=b_{ij}(0)e^{-\alpha t}+\sum_{k:\,t_k<t}H(t-t_k)\,e^{-\alpha(t-t_k)},$$

with $H$ the Heaviside function; equivalently $b_{ij}'=-\alpha b_{ij}$ between interaction times, with unit increments at the $t_k$.

**Discretization.** With a time step $\Delta t$ and snapshots $\mathbf B^{(\tau)}=\mathbf B(\tau\Delta t)$, $\tau=0,1,2,\dots$,

$$\mathbf B^{(\tau)}=e^{-\alpha\Delta t}\,\mathbf B^{(\tau-1)}+\mathbf A^{(\tau)},$$

where $\mathbf A^{(\tau)}$ is the symmetric $0/1$ indicator matrix of the interactions occurring in $((\tau-1)\Delta t,\tau\Delta t]$ (at most one interaction per step when $\Delta t$ is small enough). Unlike a temporal network built by binning interactions into fixed windows, the tie strengths retain a memory of all past contacts, weighted by recency.

## Expansion

The recursion follows from the closed form: over one step every existing tie is multiplied by $e^{-\alpha\Delta t}$ and each new contact adds $1$. Large $\alpha$ makes the network forget quickly, so $\mathbf B^{(\tau)}$ is close to the current contact pattern; small $\alpha$ accumulates contacts, so repeated pairs dominate. When tie strengths drive transmission, the decay rate thus interpolates between instantaneous-contact and aggregated-network descriptions of spread.

## Sources

- Q. Chen and M. A. Porter, *Epidemic thresholds of infectious diseases on tie-decay networks*, arXiv:2009.12932 (2020), Section 2 (Model Setup). <https://doi.org/10.48550/arXiv.2009.12932>
