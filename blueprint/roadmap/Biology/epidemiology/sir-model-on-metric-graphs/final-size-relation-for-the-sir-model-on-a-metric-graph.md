# Final-size relation for the SIR model on a metric graph

Consider the [SIR PDE–ODE model on a metric graph](sir-pde-ode-model-on-a-metric-graph-and-mass-conservation.md) with its standing hypotheses and well-prepared initial data ($S_v^0 > 0$, $\sum_v I_v^0 > 0$, $u_e^0 \ge 0$ satisfying the exchange condition), and let $M^0$ be the initial total mass. Write $\mathcal I_v(t) = \int_0^t I_v(s)\, ds$ for the cumulative infected population at vertex $v$.

**Theorem (Besse and Faye 2021, Theorem 2).** As $t \to \infty$, $u_e(t,x) \to 0$ for every edge $e$ and $x \in \Omega_e$, with $\int_0^\infty u_e(s,v)\, ds < \infty$ at each endpoint $v$ of $e$; the limits $\mathcal I_v^\infty = \lim_{t\to\infty} \mathcal I_v(t)$ satisfy $0 < \mathcal I_v^\infty < \infty$, and

$$\lim_{t\to\infty} \bigl(S_v(t), I_v(t), R_v(t)\bigr) = \bigl(S_v^0 e^{-\tau_v \mathcal I_v^\infty},\ 0,\ \eta_v \mathcal I_v^\infty\bigr), \qquad v \in \mathcal V.$$

The vector $(\mathcal I_v^\infty)_{v}$ solves the system

$$S_v^0 e^{-\tau_v \mathcal I_v^\infty} + \eta_v \mathcal I_v^\infty = I_v^0 + S_v^0 + \sum_{e\sim v} \alpha_e^v \int_0^\infty u_e(s,v)\,ds - \bar\lambda_v \mathcal I_v^\infty \quad (v \in \mathcal V),$$

$$\sum_{v} \int_0^\infty \langle A_v \mathbf u_v(s), \mathbf 1\rangle\, ds = \sum_{e} \int_{\Omega_e} u_e^0(x)\,dx + \sum_v \bar\lambda_v \mathcal I_v^\infty,$$

and consequently lies on the hypersurface

$$\sum_{v\in\mathcal V} \Bigl(S_v^0 e^{-\tau_v \mathcal I_v^\infty} + \eta_v \mathcal I_v^\infty\Bigr) = M^0.$$

Equivalently $\sum_v (S_v^\infty + R_v^\infty) = M^0$: no infected individuals remain on the edges or at the vertices.

**Corollary (equal final values; Lemma 4.4).** Suppose $\tau_v = \tau$, $\eta_v = \eta$ and $S_v^0 = S^0$ for all $v$, and suppose the final cumulative values are all equal, $\mathcal I_v^\infty = \mathcal I^\infty$ for all $v$. This equality is an assumption here, not part of the definition of symmetry: Besse and Faye derive it in the fully symmetric configuration of Lemma 4.4, which also prescribes the edge lengths and diffusivities, the initial vertex values, the exchange coefficients and the symmetry of the initial edge data about the edge midpoints. Then, with $c_{\mathcal V} = |\mathcal V|$, $\mathscr R_0 = \tau M^0/\eta$ and $\mathscr R_e = \tau S^0/\eta$, the argument $-\mathscr R_e e^{-\mathscr R_0/c_{\mathcal V}}$ lies in $(-e^{-1}, 0)$ and

$$\mathcal I^\infty = \frac{W_0\bigl(-\mathscr R_e\, e^{-\mathscr R_0/c_{\mathcal V}}\bigr)}{\tau} + \frac{\mathscr R_0}{c_{\mathcal V}\, \tau},$$

where $W_0(x)$ is the principal branch of the Lambert $W$ function: the unique $y > -1$ with $y e^y = x$.

## Depends on

- [SIR PDE–ODE model on a metric graph and conservation of total population](sir-pde-ode-model-on-a-metric-graph-and-mass-conservation.md)

## Proof depends on

- [Principal-branch preimages of the Lambert map](../../../Analysis/special-functions/elementary-transcendental-functions/lambert-w-function/exists-unique-lambert-map-preimage.md): existence and uniqueness of $W_0(x)$ for $x > -e^{-1}$, which identifies the solution of the symmetric final-size equation.

## Expansion

Integrating $S_v' = -\tau_v S_v I_v$ gives $S_v(t) = S_v^0 e^{-\tau_v \mathcal I_v(t)}$, and $R_v = \eta_v \mathcal I_v$. Mass conservation and the monotonicity of $S_v$ and $R_v$ give integrability of $I_v$ and of the edge fluxes; a compactness argument on time translates shows the edge densities converge to a solution of the heat equation with zero Dirichlet and Neumann data, hence to $0$. Integrating the $I_v$ equation in time and passing to the limit gives the vertex identities, and summing them with the edge mass balance gives the hypersurface. In the symmetric case the hypersurface reduces to $S^0 e^{-\tau \mathcal I} + \eta\mathcal I = M^0/c_{\mathcal V}$; setting $y = M^0/(c_{\mathcal V}\eta) - \mathcal I$ turns it into $(-\tau y)e^{-\tau y} = -\mathscr R_e e^{-\mathscr R_0/c_{\mathcal V}}$, solved by the Lambert $W$ function. The equation $g(\mathcal I) = S^0 e^{-\tau\mathcal I} + \eta\mathcal I - M^0/c_{\mathcal V} = 0$ has exactly one positive root, because $g$ is strictly convex with $g(0) = S^0 - M^0/c_{\mathcal V} < 0$ (since $M^0 \ge c_{\mathcal V}S^0 + \sum_v I_v^0 > c_{\mathcal V}S^0$); there $g' > 0$, that is $\tau S^0 e^{-\tau\mathcal I} < \eta$, which reads $-\tau y > -1$. The same mass bound gives $\mathscr R_0/c_{\mathcal V} > \mathscr R_e$, so $\mathscr R_e e^{-\mathscr R_0/c_{\mathcal V}} < \mathscr R_e e^{-\mathscr R_e} \le e^{-1}$. Hence $-\tau y$ is the unique preimage greater than $-1$, namely $W_0(-\mathscr R_e e^{-\mathscr R_0/c_{\mathcal V}})$. For one vertex and no edges the hypersurface would reduce to the classical [Kermack–McKendrick final-size equation](../kermack-mckendrick-sir-model/final-size-eq.md).

## Sources

- C. Besse and G. Faye, "Dynamics of epidemic spreading on connected graphs", Journal of Mathematical Biology (2021), <https://doi.org/10.1007/s00285-021-01602-5>, PMCID PMC8051836 (Theorem 2, equations (4.5)–(4.7), Remarks 4.1–4.2, Lemma 4.4).
