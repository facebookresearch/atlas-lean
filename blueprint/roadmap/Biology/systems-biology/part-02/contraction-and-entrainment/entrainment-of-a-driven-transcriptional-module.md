# Entrainment of a driven transcriptional module

A transcription factor $X$ (concentration $x$) is produced at a rate given by an input $u(t) \ge 0$, degraded or diluted at rate $\delta > 0$, and binds reversibly to a promoter $E$ to form a complex $C$ (concentration $y$) with binding rate $k_2 > 0$ and dissociation rate $k_1 > 0$. The total promoter $e_T > 0$ is conserved, so $[E] = e_T - y$ and

$$\dot x = u(t) - \delta x + k_1 y - k_2 (e_T - y)\, x, \qquad \dot y = -k_1 y + k_2 (e_T - y)\, x, \tag{12}$$

on the invariant set $\mathcal X = \{(x,y) : x \ge 0,\ 0 \le y \le e_T\}$.

1. **Contraction.** For all positive constants $\delta, k_1, k_2, e_T$, system (12) is infinitesimally contracting on $\mathcal X$ in the weighted norm $|(x,y)|_{1,P} = p_1|x| + p_2|y|$ for any weights with

$$1 < \frac{p_2}{p_1} < 1 + \frac{\delta}{k_2 e_T},$$

with contraction rate $c = \min\bigl\{\delta - (p_2/p_1 - 1)k_2 e_T,\ (1 - p_1/p_2)\,k_1\bigr\} > 0$, uniformly in the input $u$.
2. **Entrainment.** For every nonnegative $T$-periodic input $u$, all solutions of (12) in $\mathcal X$ converge exponentially to a unique periodic solution of period $T$.

## Depends on

- [Entrainment of contracting systems to periodic inputs](entrainment-of-contracting-systems-to-periodic-inputs.md)

## Expansion

The input enters additively, so the Jacobian does not depend on $u$:

$$J = \begin{pmatrix} -\delta - k_2(e_T - y) & k_1 + k_2 x \\ k_2 (e_T - y) & -k_1 - k_2 x \end{pmatrix}.$$

With $P = \mathrm{diag}(p_1, p_2)$, the measure $\mu_1(PJP^{-1})$ is the larger of the two column sums $-\delta + (p_2/p_1 - 1)k_2(e_T - y)$ and $-(1 - p_1/p_2)(k_1 + k_2 x)$. Because $0 \le e_T - y \le e_T$ and $x \ge 0$, the stated weight range makes both at most $-c$. Item 2 then follows from the entrainment theorem for contracting systems on the closed convex set $\mathcal X$. The contraction rate, and hence the convergence speed, grows with the degradation rate $\delta$. The same weighted-norm argument covers a transcription factor activated from an inactive form by a periodically varying kinase, and several downstream modules driven by one factor. Driving the module with a repeating signal produces a repeating output of the same period, whatever the initial state.

## Sources

- G. Russo, M. di Bernardo, E. D. Sontag, "Global entrainment of transcriptional systems to periodic inputs", *PLoS Computational Biology* (2010), Results ("Mathematical model and problem statement", Eqs. (11)–(12), Propositions 1–2, proof of Proposition 1 via Eqs. (14)–(25), and "Generalizations"), <https://doi.org/10.1371/journal.pcbi.1000739> (PMC2855316).
