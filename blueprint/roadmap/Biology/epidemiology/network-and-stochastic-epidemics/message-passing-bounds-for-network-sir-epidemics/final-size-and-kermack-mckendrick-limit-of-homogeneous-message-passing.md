# Final size and Kermack–McKendrick limit of homogeneous message passing

On an $n$-regular arc-transitive graph with identically distributed individuals (initial susceptible probability $z$, vaccinated probability $y$, $0 < z < 1$, $0 \le y < 1 - z$), the message-passing system reduces to

$$S_{\mathrm{mes}} = z F^n, \qquad F(t) = 1 - \int_0^t f(\tau)\bigl(1 - y - z F(t-\tau)^{n-1}\bigr)d\tau, \qquad R_{\mathrm{mes}}(t) = y + \int_0^t r(\tau)\bigl[1 - y - S_{\mathrm{mes}}(t-\tau)\bigr]d\tau,$$

where $f$ is the density of the time from infection to an infectious contact along one edge and $p = \int_0^\infty f \in [0,1]$ is the per-edge transmissibility. For Poisson contacts at rate $\beta$ and recovery at rate $\gamma$, $f(\tau) = \beta e^{-(\beta+\gamma)\tau}$ and $\dot F = \gamma(1 - F) - \beta(F - y - zF^{n-1})$.

**Theorem 4 (final size and no major outbreak).** For all $t \ge 0$, $S_{\mathrm{mes}}(\infty) \le P_S(t)$ and $R_{\mathrm{mes}}(\infty) \ge P_R(t)$, where $S_{\mathrm{mes}}(\infty)$ is the unique solution in $[0, z]$ of

$$\left(\frac{S_{\mathrm{mes}}(\infty)}{z}\right)^{1/n} = 1 - p + p\,y + p\,z\left(\frac{S_{\mathrm{mes}}(\infty)}{z}\right)^{(n-1)/n},$$

and $R_{\mathrm{mes}}(\infty) = 1 - S_{\mathrm{mes}}(\infty)$. With $R_0 := (n-1)p$, as the initially infected fraction vanishes ($z \uparrow 1 - y$), $P_S(\infty) = P_S(0)$ whenever $R_0 \le 1$ or $y \ge 1 - 1/R_0$: vaccinating a fraction at least $1 - 1/R_0$ prevents a major outbreak. If moreover $n \to \infty$ with $(n-1)p \to R_0$, the relation becomes $\dfrac{S(\infty)}{1-y} = e^{-R_0(1 - S(\infty) - y)}$.

**Theorem 6 (Kermack–McKendrick limit).** Let $f = f_n$ depend on $n$ with $n f_n \to f^*$ uniformly on $[0,T]$ and $\sup_{[0,T]} f^* < \infty$ for every $T > 0$, each $f_n$ continuously differentiable, and fixed initial conditions $(z, 1-z-y, y)$. Then for every $T > 0$, $\sup_{0 \le t \le T}|S^{(n)}_{\mathrm{mes}}(t) - S(t)| \to 0$ (and likewise for $I$, $R$), where

$$\dot S(t) = S(t)\int_0^t f^*(\tau)\,\dot S(t-\tau)\,d\tau - I(0) f^*(t), \qquad R(t) = R(0) + \int_0^t r(\tau)\bigl[1 - R(0) - S(t-\tau)\bigr]d\tau$$

is the Kermack–McKendrick model with $I = 1 - S - R$. In the Markovian case, $S(t) < S_{\mathrm{mes}}(t) \le P_S(t)$ and $R(t) > R_{\mathrm{mes}}(t) \ge P_R(t)$ for $t > 0$, so message passing approximates the stochastic epidemic better than Kermack–McKendrick does.

## Expansion

Since $F$ is non-increasing and bounded, it has a limit $F(\infty)$, and dominated convergence in the integral equation gives $F(\infty) = 1 - p(1 - y - zF(\infty)^{n-1})$; substituting $F = (S/z)^{1/n}$ yields the final-size equation, whose uniqueness in $[0,z]$ follows by convexity. Linearizing at $S = z = 1 - y$ shows that the only solution is the trivial one exactly when $(n-1)p(1-y) \le 1$. The quantity $(n-1)p$ is the mean number of further infections an infected individual causes along its non-parental edges. In the large-degree limit each edge carries transmissibility $O(1/n)$, the cavity product becomes an exponential of an integral, and the message-passing integral equation converges, by a Gronwall argument, to the Kermack–McKendrick renewal equation. This makes the classical deterministic model a provable upper bound for the mean of the underlying network epidemic.

## Depends on

- [Message passing bounds the stochastic SIR epidemic on any graph](message-passing-bounds-the-stochastic-sir-epidemic-on-any-graph.md)

## Proof depends on

- [Dominated convergence theorem for nonnegative functions](../../../../MeasureTheory/integration/dominated-convergence-theorem/tendsto-lintegral-of-dominated-convergence.md)
- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- R. R. Wilkinson, F. G. Ball, K. J. Sharkey, "The relationships between message passing, pairwise, Kermack–McKendrick and stochastic SIR epidemic models", Journal of Mathematical Biology (2017), Eqs. (9)–(21) and (30)–(33), Theorem 4, Remark 1, Corollary 3, Theorem 6 and Corollary 4, <https://doi.org/10.1007/s00285-017-1123-8>, PMCID PMC5641366.
