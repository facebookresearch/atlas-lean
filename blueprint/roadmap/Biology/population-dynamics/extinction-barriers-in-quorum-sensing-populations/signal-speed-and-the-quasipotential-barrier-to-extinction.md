# Signal speed and the quasipotential barrier to extinction

**Model.** Cell density $x$ and signal density $w$ change in steps of $1/N$ through four channels: division at total rate $Nx\,b(w)$ with a Hill-type increasing $b$, death at rate $Nx\,d(x)$ (including the production cost $c$ and crowding), signal production at rate $Nr\alpha x$ and signal removal at rate $Nr\kappa w$, where $r>0$ scales both signal channels. As $N\to\infty$ the density process converges on compact time intervals to the mean-field system (Kurtz's law of large numbers, Theorem 1)

$$\dot x=x\big[b(w)-d(x)\big],\qquad \dot w=r\big[\alpha x-\kappa w\big].$$

Write $\bar w(x)=\alpha x/\kappa$, $\bar b(x)=b(\bar w(x))$ and $\bar F(x)=x[\bar b(x)-d(x)]$ for the slaved drift.

**Proposition 2 (r-independence of the deterministic picture).** Every equilibrium $(x_{\rm eq},w_{\rm eq})$ satisfies $w_{\rm eq}=\bar w(x_{\rm eq})$ and $\bar F(x_{\rm eq})=0$, independently of $r$. If $x_{\rm eq}>0$, the Jacobian satisfies $\det J_r=-r\kappa\bar F'(x_{\rm eq})$ and $\operatorname{tr}J_r=-x_{\rm eq}d'(x_{\rm eq})-r\kappa<0$, so for every $r$ the equilibrium is a saddle if $\bar F'(x_{\rm eq})>0$ and asymptotically stable if $\bar F'(x_{\rm eq})<0$. The extinction state $(0,0)$ has eigenvalues $b_0-d_0-c$ and $-r\kappa$, so it is stable for every $r$ when $b_0<d_0+c$.

**Proposition 7 (saddle barrier).** In the bistable regime (extinction $U_{\rm off}$, saddle $U_*$, cooperative state $U_{\rm on}$), let $V^Q_r$ be the Freidlin–Wentzell quasipotential from $U_{\rm on}$ for the jump process restricted to the open quadrant, and $\Delta V(r)$ its value at the saddle $U_*$. For every neighbourhood $R$ of $U_{\rm off}$ inside its basin of attraction, $\inf_{z\in R}V^Q_r(z)=\Delta V(r)$: the cheapest way to reach the extinction basin is through the saddle, and under metastability assumptions the mean extinction time grows like $e^{N\Delta V(r)}$.

**Numerical finding.** Minimum-action computations give $\Delta V(r)=\Delta V_\infty+O(1/r)$, where $\Delta V_\infty$ is the barrier of the one-dimensional slaved model; at $r=1$ the barrier is $55\%$ larger than $\Delta V_\infty$. Mean extinction times from the backward equation on a truncated lattice and from exact simulation grow at rates matching $\Delta V(r)$.

## Expansion

Proposition 2 holds because the $w$-nullcline $w=\bar w(x)$ and the $x$-nullcline do not involve $r$; at a positive equilibrium the Jacobian is $\begin{pmatrix}-xd'&xb'(w)\\ r\alpha&-r\kappa\end{pmatrix}$, whose determinant is $r\kappa$ times $-\bar F'$. The large-deviation rate function, however, depends on the full noise structure of all four channels, which scales with $r$ on the signal coordinate, so the optimal escape path changes. Slow signals lag behind cell density: a downward fluctuation in $x$ leaves $w$ temporarily high, which keeps division high and raises the cost of escape. Proposition 7 also shows that crossing a density threshold is cheaper than entering the extinction basin, since paths keeping the signal high usually recover.

## Sources

- M. Ayala, J. Zimmer, "Computing Extinction Barriers in a Quorum-Sensing Reaction Network", arXiv preprint (2026), Theorem 1 (Kurtz), Propositions 2, 3 and 7, and the numerical results on $\Delta V(r)$, <https://doi.org/10.48550/arXiv.2609.39946>.
