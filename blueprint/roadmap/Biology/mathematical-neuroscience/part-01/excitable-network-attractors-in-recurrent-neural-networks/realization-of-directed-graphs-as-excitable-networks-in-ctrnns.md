# Realization of directed graphs as excitable networks in CTRNNs

**Model.** A continuous-time recurrent neural network (CTRNN) on $N$ cells is

$$\dot y_i=-y_i+\sum_{j=1}^N w_{ij}\,\phi(y_j)+I_i(t),\qquad i=1,\dots,N,$$

with a sigmoid activation $\phi$; it is *input-free* if $I\equiv0$. Take the piecewise affine activation with threshold $\theta$ and steepness $\epsilon>0$,

$$\phi_P(y)=\begin{cases}0,& y-\theta<-2\epsilon,\\ \frac{y-\theta}{4\epsilon}+\frac12,& |y-\theta|\le2\epsilon,\\ 1,& y-\theta>2\epsilon.\end{cases}$$

Given a directed graph $G$ with adjacency matrix $(a_{ij})$, define the weights

$$w_{ij}=w_t+(w_s-w_t)\delta_{ij}+(w_p-w_t)a_{ji}+(w_m-w_t)a_{ij},$$

so $w_{ii}=w_s$ (self-excitation), $w_{ij}=w_p$ if $G$ has an edge $j\to i$, $w_{ij}=w_m$ if $G$ has an edge $i\to j$, and $w_{ij}=w_t$ otherwise.

**Excitable network attractor.** A set of stable equilibria $\xi_1,\dots,\xi_N$ together with *excitable connections*: there is a connection $\xi_k\to\xi_l$ with threshold $\delta$ if some trajectory starting within distance $\delta$ of $\xi_k$ converges to $\xi_l$. The network *realizes* $G$ if every edge $k\to l$ of $G$ is present as such a connection.

**Theorem 1.** Let $G$ be a directed graph on $N$ vertices with no loops of order one ($a_{ii}=0$), no loops of order two ($a_{ij}a_{ji}=0$) and no $\Delta$-cliques ($a_{ij}a_{ik}a_{jk}=0$ for all $i,j,k$). For every sufficiently small $\delta>0$ there is an open set $W_{ex}\subset\mathbb R^6$ of parameters $(\epsilon,\theta,w_s,w_m,w_t,w_p)$ such that the input-free CTRNN with activation $\phi_P$ and the weights above has an excitable network attractor with threshold $\delta$ that realizes $G$, with one stable equilibrium per vertex.

## Expansion

If cell $k$ is saturated on ($\phi(y_k)=1$) and every other cell is off ($\phi(y_j)=0$), the equilibrium equations give $y_i=w_{ik}$, i.e. $\xi_k$ has $y_k=w_s$, $y_i=w_p$ for successors $i$ of $k$, $y_i=w_m$ for predecessors and $y_i=w_t$ otherwise. This is a consistent stable equilibrium when $w_s>\theta+2\epsilon$ and $w_p,w_m,w_t<\theta-2\epsilon$. If $w_p$ lies within $\delta$ below the threshold region, a perturbation of size $\delta$ that raises a successor cell $l$ switches it on; its self-excitation then sustains it, while the inhibitory weight $w_m$ from $l$ back to its predecessor $k$ switches $k$ off, so the trajectory converges to $\xi_l$. The exclusions of short loops and triangles prevent a cell from receiving the excitatory and inhibitory weights simultaneously, or from switching on a third cell along a shortcut, which would create spurious transitions. Driving the network with input pulses then implements an arbitrary finite-state machine on $G$, and noise produces intermittent dynamics with long dwell times near the states.

## Sources

- Ashwin P, Postlethwaite C, "Excitable networks for finite state computation with continuous time recurrent neural networks", Biological Cybernetics (2021), Equations (1)-(8), Theorem 1 and Appendix B, <https://doi.org/10.1007/s00422-021-00895-5>, PMCID PMC8589808.
