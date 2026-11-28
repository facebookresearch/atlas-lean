# SIR PDE–ODE model on a metric graph and conservation of total population

Let $\mathcal G = (\mathcal V, \mathcal E)$ be a finite connected compact metric graph; each edge $e$ is a segment $\Omega_e = [0, \ell_e]$ with $\ell_e \in (0, \infty)$, and $\delta_v \ge 1$ is the number of edges incident to the vertex $v$ (written $e \sim v$). At each vertex $v$ the susceptible, infected and removed populations $(S_v, I_v, R_v)$ satisfy

$$S_v' = -\tau_v S_v I_v, \qquad I_v' = \tau_v S_v I_v - \eta_v I_v + \sum_{e \sim v} \alpha_e^v\, u_e(t, v) - \bar\lambda_v I_v, \qquad R_v' = \eta_v I_v,$$

with $\tau_v, \eta_v > 0$ and $\bar\lambda_v = \sum_{e\sim v} \lambda_e^v$. Infected individuals on edge $e$ have density $u_e(t,x)$ with $\partial_t u_e = d_e\, \partial_x^2 u_e$ ($d_e > 0$) in the interior of $\Omega_e$. At each vertex the vector $\mathbf u_v = (u_e(t,v))_{e\sim v}$ satisfies the exchange condition

$$D_v\, \partial_n \mathbf u_v + K_v\, \mathbf u_v = \Lambda_v \mathbf I_v,$$

where $\partial_n$ is the outward normal derivative, $D_v = \operatorname{diag}(d_e)_{e\sim v}$, $\Lambda_v = \operatorname{diag}(\lambda_e^v)_{e \sim v}$, $\mathbf I_v = (I_v, \dots, I_v)^{\top} \in \mathbb R^{\delta_v}$, and $K_v = A_v + N_v$ with $A_v = \operatorname{diag}(\alpha_e^v)_{e\sim v}$ and $N_v$ the edge-to-edge exchange matrix with diagonal entries $\sum_{e' \ne e} \nu^v_{e,e'}$ and off-diagonal entries $(N_v)_{e,e'} = -\nu^v_{e',e}$, so that **every column of $N_v$ sums to zero**. The standing hypotheses are $\alpha_e^v, \lambda_e^v \in (0,1)$, $\sum_{e\sim v} \alpha_e^v \in (0,1)$, $\sum_{e\sim v}\lambda_e^v \in (0,1)$, $\nu^v_{e,e'} \in [0,1)$, $(K_v)_{e,e} \in (0,1)$, and the row diagonal dominance $\sum_{e' \ne e} \nu^v_{e',e} < \alpha_e^v + \sum_{e'\ne e} \nu^v_{e,e'}$ (automatic when every $N_v$ is symmetric).

**Theorem (well-posedness; Besse and Faye 2021, Theorem 1).** For initial data $S_v^0 > 0$, $I_v^0 \ge 0$ with $\sum_v I_v^0 > 0$, $R_v^0 = 0$, and bounded continuous $u_e^0 \ge 0$ satisfying the exchange condition at $t = 0$, the system has a unique positive global classical solution, $C^1$ in time at the vertices and $C^{1,2}$ on $(0,\infty) \times \mathcal G$ along the edges.

**Proposition (conservation of total population; Section 2.4).** For such a solution, the total mass

$$M(t) = \sum_{e\in\mathcal E} \int_{\Omega_e} u_e(t,x)\, dx + \sum_{v\in\mathcal V} \bigl(S_v(t) + I_v(t) + R_v(t)\bigr)$$

is constant: $M(t) = M^0$ for all $t \ge 0$.

## Proof depends on

- [Gronwall inequality in integral form](../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md): for uniqueness, applied to the difference of two solutions.

## Expansion

At a vertex, $(S_v + I_v + R_v)' = \langle A_v \mathbf u_v, \mathbf 1\rangle - \langle \Lambda_v \mathbf I_v, \mathbf 1\rangle$. On the edges, integrating the heat equation gives $m'(t) = \sum_e d_e [\partial_x u_e]_{\partial\Omega_e} = \sum_v \langle D_v \partial_n \mathbf u_v, \mathbf 1\rangle = \sum_v \langle \Lambda_v \mathbf I_v - A_v \mathbf u_v - N_v \mathbf u_v, \mathbf 1 \rangle$, and $\langle N_v \mathbf u_v, \mathbf 1\rangle = 0$ because the columns of $N_v$ sum to zero. The two contributions cancel. Existence is proved by an iteration that alternates the vertex ODEs and the edge heat equations with inhomogeneous Robin data, using the column and row diagonal dominance of $K_v$ for a priori bounds; uniqueness follows from a Gronwall estimate. Without edges, the vertex equations reduce to the classical SIR model at each vertex, whose [final-size equation](../kermack-mckendrick-sir-model/final-size-eq.md) the metric-graph final-size relation generalises.

## Sources

- C. Besse and G. Faye, "Dynamics of epidemic spreading on connected graphs", Journal of Mathematical Biology (2021), <https://doi.org/10.1007/s00285-021-01602-5>, PMCID PMC8051836 (model (2.1)–(2.3), Hypotheses 2.1–2.2, Section 2.4, Theorem 1).
