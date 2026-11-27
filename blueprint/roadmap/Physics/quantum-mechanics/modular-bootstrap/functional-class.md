# Odd radial functionals, vacuum feasibility, and last sign threshold

For fixed $c\ge40$ let $\overline{\mathcal A}$ consist of real continuous $g:[0,\infty)\to\mathbb R$ with $\int_0^\infty|g|\,dt<\infty$, $\widehat g=-g$ on $[0,\infty)$ for the [radial transform](radial-j0-transform.md), and finite [Cardy-weighted mass](cardy-weight.md) $M[g]$. No differentiability, analytic continuation, or prescribed decay rate is an additional membership hypothesis.

For $0<\alpha\le a$, define the value below the threshold by

$$
 g(-\alpha)=-2\pi\int_0^\infty g(t)K_\alpha(t)\,dt.
$$

The formula agrees at $\alpha=0$ with the value given by $\widehat g(0)=-g(0)$. The integrals are absolutely convergent. Then $g_{\mathrm{vac}}=g(-a)-2g(1-a)+g(2-a)=-\int_0^\infty g(t)\rho_C(t)\,dt$. Feasibility at a real threshold $T$ means $g(t)\ge0$ on the allowed tail $t\ge T$ and $g_{\mathrm{vac}}>0$; weak feasibility retains the tail condition and only asks $g_{\mathrm{vac}}\ge0$. Without a named threshold, either word means the respective condition holds at some $T$. The last sign threshold is $t_1(g)=\inf\{T:g\ge0\text{ on }[T,\infty)\}$, with the sign condition applied where $g$ is defined. For a nonzero weakly feasible function this is a finite, nonnegative threshold, reached by continuity. The strict positive vacuum condition is essential for certification; zero vacuum action is not interchangeable with it.

## Depends on

- [Planar radial transform](radial-j0-transform.md)
- [Cardy weight and vacuum action](cardy-weight.md)

## Expansion

Break out the comparison between $K_\alpha$ and $V$, including at $\alpha=a$, to prove absolute convergence and continuity of the below-threshold extension and compatibility at zero. Establish the paper's zero-threshold exclusion for nonzero weakly feasible functions. The negative part of such a function is supported in $[0,t_1(g)]$, and weak vacuum feasibility then gives $\int_0^{t_1(g)}\max(-g(t),0)V(t)\,dt\ge M[g]/2$. Prove separately that compactly supported finite-order distributions in $\beta\in(0,\infty)$ applied to the crossing kernel give members, including odd Laguerre derivative functionals of every finite order (Lemma 2.6).

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Definition 2.3 and (2.5), p. 9](https://hexagonmath.org/pdf/2611.00174v1#page=9).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [(2.14)–(2.16), p. 11](https://hexagonmath.org/pdf/2611.00174v1#page=11).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Definition 2.5, pp. 13–14](https://hexagonmath.org/pdf/2611.00174v1#page=13).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [below-threshold extension and Lemma 2.6, p. 14](https://hexagonmath.org/pdf/2611.00174v1#page=14).
