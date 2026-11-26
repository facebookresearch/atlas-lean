# Two-phase ageing model with competition

**Setting.** A wild population is split into a first ageing phase (density $N_1$) and a second, post-transition phase (density $N_2$). Phase-1 individuals reproduce at rate $b>0$, phase-2 individuals at rate $\tilde b\ge 0$, and all newborns enter phase 1. Phase-1 individuals pass into phase 2 at rate $k+\eta_1N_1+\eta_2N_2$ (a baseline transition rate $k>0$ accelerated by competition) and die from competition at rate $c_1N_1+c_2N_2$; phase-2 individuals die at rate $d+\tilde c_1N_1+\tilde c_2N_2$ with $d>0$. All competition coefficients $\eta_i,c_i,\tilde c_i$ are nonnegative. With constant rates this is the planar system
$$\begin{aligned}\dot N_1&=bN_1+\tilde bN_2-\bigl(k+(\eta_1+c_1)N_1+(\eta_2+c_2)N_2\bigr)N_1,\\ \dot N_2&=\bigl(k+\eta_1N_1+\eta_2N_2\bigr)N_1-\bigl(d+\tilde c_1N_1+\tilde c_2N_2\bigr)N_2,\end{aligned}$$
on $\mathbb R_{\ge0}^2$. Write $c_1^{\mathrm{tot}}=\eta_1+c_1$. The quantity $R=b/k+\tilde b/d$ is the expected offspring number of a newborn in the absence of competition (time $1/k$ in phase 1, then time $1/d$ in phase 2, the transition being certain).

**Theorem 3.1 (no periodic orbits).** The system has no periodic orbit lying entirely in $\mathbb R_{\ge0}^2$.

**Theorem 3.2 (persistence).** Suppose $c_1^{\mathrm{tot}}>0$, $\tilde c_2>0$, $R>1$ and $N_1(0)>0$. Then, for $\tilde b$ small enough, there is a single globally stable positive steady state $(N_1^*,N_2^*)$. If moreover $b<k$, then $N_1^*$ and $N_2^*$ are of order $O(\tilde b)$ as $\tilde b\to0$.

**Theorem 3.3 (extinction).** Suppose $c_1^{\mathrm{tot}}>0$, $\tilde c_2>0$ and $R<1$. Then, for $\tilde b$ small enough, $(0,0)$ is the unique steady state, it is stable, and every trajectory converges to it.

## Expansion

Linearizing at the origin gives the matrix $\begin{pmatrix}b-k&\tilde b\\k&-d\end{pmatrix}$, whose determinant $(k-b)d-k\tilde b=kd(1-R)$ changes sign exactly at $R=1$; so $R$ plays the role of the basic reproduction number. Absence of periodic orbits follows from Dulac's criterion with the weight $1/(N_1N_2)$, under which the divergence of the vector field is strictly negative on the open quadrant because competition only increases loss rates. Bounded trajectories then converge to equilibria by the Poincaré-Bendixson theorem. For $R>1$ uniqueness of the positive equilibrium is shown by reducing the steady-state equations to a single polynomial and using the smallness of $\tilde b$; when $b<k$ the population is sustained only through the small phase-2 fecundity, so its equilibrium size scales with $\tilde b$. The paper also proves well-posedness of the full age-structured PDE version (Theorem 2.3) and local and global convergence for a PDE-ODE hybrid (Theorems 4.1, 4.2 and 4.5).

## Sources

- L. Breuil, "Stability analysis and long-time convergence of a partial differential equation model of two-phase ageing", arXiv preprint (2026), Theorem 2.3, Theorem 3.1, Theorem 3.2, Theorem 3.3, Theorems 4.1, 4.2 and 4.5, <https://doi.org/10.48550/arXiv.2603.19814>.
