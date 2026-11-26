# Global attraction of the activator-inhibitor receptor occupancy equilibrium

Free receptor sites $R$ on cell-surface sensors bind either an activating ligand $L$ (for example the chemokine CXCL12 acting on melanoma cells) or an inhibiting drug $X$:

$$R+L\ \underset{k_{-1}}{\overset{k_1}{\rightleftharpoons}}\ P,\qquad R+X\ \underset{k_{-2}}{\overset{k_2}{\rightleftharpoons}}\ Q,$$

where $P$ and $Q$ are the numbers of sites occupied by the activator and by the inhibitor. Over the time span of an assay the totals $L_0=P+L$, $X_0=Q+X$ and $R_0=P+Q+R$ are conserved, and mass-action kinetics reduce to

$$\frac{dP}{dt}=k_1(R_0-P-Q)(L_0-P)-k_{-1}P,\qquad\frac{dQ}{dt}=k_2(R_0-P-Q)(X_0-Q)-k_{-2}Q,$$

with all parameters positive. The physically meaningful states form $D=\{(P,Q):0\le P\le L_0,\ 0\le Q\le X_0\}$.

**Theorem.**

1. There is a unique equilibrium $(P^*,Q^*)$ in the interior of $D$.
2. It is a stable proper node, hence locally asymptotically stable.
3. $D$ is positively invariant: solutions starting in $D$ exist for all $t>0$ and stay in $D$.
4. $D$ lies in the basin of attraction of $(P^*,Q^*)$.

The Jacobian at $(P^*,Q^*)$ has two distinct negative eigenvalues $-\lambda$ and $-\mu$ with $0<\lambda<\mu$, so trajectories first approach a slow manifold and then slide along it. When $k_1=k_2$ and $k_{-1}=k_{-2}$,
$$\lambda=k_1(R_0-P^*-Q^*),\qquad\mu=\lambda+k_1(L_0+X_0-P^*-Q^*),$$
and the slow and fast manifolds are the lines $P+Q=P^*+Q^*$ and $Q^*P-P^*Q=0$. When binding is much faster than unbinding ($k_1R_0\gg k_{-1}$, $k_2R_0\gg k_{-2}$), receptors fill quickly and the subsequent competition is slow, which is the regime used to fit viability measurements over time and to derive $IC_{50}(t)$ curves.

## Expansion

The interior equilibrium is the unique intersection of the two nullclines in $D$: solving $\dot P=0$ for $Q$ gives a continuous decreasing function of $P$ on $[0,L_0)$, and similarly for $\dot Q=0$, so the two curves cross exactly once. The off-diagonal Jacobian entries $-k_1(L_0-P)$ and $-k_2(X_0-Q)$ have the same sign, so the system is competitive in the plane and its Jacobian has real eigenvalues, both negative at the equilibrium. Invariance of $D$ and convergence of every trajectory in $D$ are shown in the appendix of the source from the direction of the vector field on the boundary of $D$ and the absence of other equilibria there.

## Sources

- R. Anguelov, G. Manjunath, A. E. Phiri and T. T. Nyakudya, "Quantifying assays: A Modeling tale of variability in cancer therapeutics assessed on cancer cells", arXiv preprint (2022), <https://doi.org/10.48550/arXiv.2207.08449>. Section 2 (activation-inhibition dynamics: reaction scheme, conservation laws, the reduced system, the set $D$, Theorem 1 with its proof in the Appendix, and the fast and slow manifolds) and Section 6 ($IC_{50}$ curves).
