# Well-posedness of the chemotactic reaction–diffusion SIR model

**Model.** On a bounded smooth domain $\Omega$ and time interval $(0,T)$, with $Q = \Omega \times (0,T)$, consider densities $s, i, r$ of susceptible, infected and removed individuals:

$$
\begin{aligned}
\partial_t s - \nabla\cdot(\nu_s\nabla s) + \frac{\beta\, i}{s+i+r}\, s &= 0,\\
\partial_t i - \nabla\cdot\bigl(\nu_i\nabla i - \chi(x,t,i)\nabla s\bigr) + \phi\, i - \frac{\beta\, s}{s+i+r}\, i &= 0,\\
\partial_t r - \nabla\cdot(\nu_r\nabla r) - \phi\, i &= 0,
\end{aligned}
$$

with no-flux boundary conditions $\nabla s\cdot\mathbf{n} = (\nu_i\nabla i - \chi(x,t,i)\nabla s)\cdot\mathbf{n} = \nabla r\cdot\mathbf{n} = 0$ and initial data $(s_0, i_0, r_0)$. Here $\beta$ is the contact rate, $\phi$ the removal rate, $\nu_s, \nu_i, \nu_r$ diffusion coefficients, and $\chi$ a chemotactic sensitivity: for $\chi > 0$ infected individuals move toward regions of higher susceptible density, mimicking airborne transmission concentrated where many hosts gather.

**Assumptions** ((3.1)–(3.6) of arXiv:2404.17506):
- $\nu_s, \nu_i, \nu_r \in L^\infty(Q)$ with $0 < \nu_m \le \nu_s, \nu_i, \nu_r \le \nu_M$ a.e. in $Q$;
- $\beta \in L^\infty(Q)$ with $0 \le \beta \le \beta_M$ a.e. in $Q$, and $\phi > 0$;
- $\chi : \Omega \times (0,T) \times \mathbb R \to \mathbb R$ is a Carathéodory function with $|\chi(x,t,v)| \le \chi_M$ and $|\chi(x,t,v)| \le \chi_{1,M}\,v$ for a.e. $(x,t) \in Q$ and all $v \ge 0$;
- $(s_0, i_0, r_0) \in L^2(\Omega)^3$, nonnegative a.e., with $s_0 \le s_M$ a.e. for a constant $s_M > 0$.

**Results.** With $H = L^2(\Omega)$, $V = H^1(\Omega)$:
1. *(Existence.)* Under these assumptions there is a weak solution $(s, i, r) \in \bigl(H^1(0,T;V') \cap C([0,T];H) \cap L^2(0,T;V)\bigr)^3$ with $0 \le s \le s_M$, $i \ge 0$, $r \ge 0$ a.e. in $Q$; it is obtained as the limit of solutions of a regularized problem in which the incidence denominator is bounded away from zero by $\varepsilon$.
2. *(Lower bound and regularity.)* Assume (3.1)–(3.6). If $s_0$ is bounded below by a positive constant, then $s \ge s_m > 0$ a.e.; if moreover $\nu_s$ is constant, $\beta \in L^2(0,T;V)$ and $s_0 \in H^2$ with the boundary condition, then $s$ is a strong solution, bounded in $H^1(0,T;V) \cap L^\infty(0,T;H^2(\Omega))$.
3. *(Uniqueness.)* Under (3.1)–(3.6) and all the hypotheses of item 2 ($s_0$ bounded below by a positive constant, $\nu_s$ constant, $\beta \in L^2(0,T;V)$ and $s_0 \in H^2$ with the boundary condition), if moreover $\chi$ is Lipschitz, $|\chi(x,t,v_1) - \chi(x,t,v_2)| \le L_M|v_1 - v_2|$ for all $v_1, v_2 \ge 0$, the weak solution is unique.
4. *(Vanishing diffusion of $s$ and $r$.)* Assume (3.1)–(3.6). If $s_0$ is bounded below by a positive constant, $\beta \in L^2(0,T;V)$ and $s_0, r_0 \in V$, then, letting $\nu_s, \nu_r \downarrow 0$ along monotone sequences, the corresponding weak solutions converge, along a subsequence, to a solution of the limiting system in which $s$ and $r$ are not diffused.

## Proof sketch

The cross-diffusion term $\nabla\cdot(\chi(x,t,i)\nabla s)$ is the Keller–Segel structure with the susceptible density playing the role of the chemoattractant. Because the $s$-equation is a diffusion with a nonnegative absorption term, the maximum principle gives $0 \le s \le s_M$, and the extra regularity of $s$ under regular data is what controls the drift term in the $i$-equation. The standard incidence $\beta si/(s+i+r)$ is singular where all densities vanish, so existence is first proved for the regularized denominator $s + i + r + \varepsilon$ and passed to the limit; uniqueness needs the Lipschitz sensitivity $\chi(x,t,\cdot)$, together with the strong-solution bound of item 2, to estimate the difference of the drift terms of two solutions. The vanishing-diffusion limit rests on a bound for $s$ in $L^\infty(0,T;V)$ uniform in $\nu_s,\nu_r$, which uses $s_0, r_0 \in V$ and $\beta \in L^2(0,T;V)$.

## Related topics

- [Kermack–McKendrick SIR model](../../kermack-mckendrick-sir-model/README.md)

## Sources

- Pierluigi Colli, Gabriela Marinoschi, Elisabetta Rocca and Alex Viguerie, "Chemotaxis-inspired PDE model for airborne infectious disease transmission: analysis and simulations", *Journal of Nonlinear Science* 35 (2025), 28, <https://doi.org/10.1007/s00332-024-10121-8>. Preprint version: arXiv:2404.17506 (2024), Theorems 3.1–3.2, Propositions 3.3–3.4, Theorems 3.5 and 4.1, <https://doi.org/10.48550/arXiv.2404.17506>.
