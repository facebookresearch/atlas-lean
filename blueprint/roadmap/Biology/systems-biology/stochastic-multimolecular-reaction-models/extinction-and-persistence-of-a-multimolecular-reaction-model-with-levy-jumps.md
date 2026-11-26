# Extinction and persistence thresholds of a multimolecular reaction model with Lévy jumps and interval parameters

**Model.** Consider the multimolecular reaction scheme

$$[\Xi_0]\xrightarrow{k_1}\Xi_1,\qquad \Xi_1\xrightarrow{k_2}Q,\qquad p\,\Xi_1+q\,\Xi_2\xrightarrow{k_3}(p+q)\,\Xi_2,\qquad \Xi_2\xrightarrow{k_4}P,$$

where $\Xi_0$ is held at constant concentration $x_0$ and $p\ge1$. Let $x(t),y(t)$ be the concentrations of $\Xi_1,\Xi_2$. The autocatalytic step is perturbed by white noise of intensity $\sigma$ and by a compensated Poisson random measure $\widetilde N(dt,du)$ with Lévy measure $\lambda$ and bounded jump sizes $\gamma(u)$:

$$\begin{aligned}
dx&=\big[k_1x_0-k_2x-pk_3x^py\big]dt-x^py\Big(\sigma\,dB+\int_{\mathbb Y}\gamma(u)\widetilde N(dt,du)\Big),\\
dy&=\big[pk_3x^py-k_4y\big]dt+x^py\Big(\sigma\,dB+\int_{\mathbb Y}\gamma(u)\widetilde N(dt,du)\Big),
\end{aligned}$$

with left limits $x(t^-),y(t^-)$ in the coefficients. *Imprecise* parameters are intervals $\hat k_i=[k_i^l,k_i^u]$, $\hat p$ and $\hat\sigma$. They are handled through the parametrization $f(\upsilon)=(f^l)^{1-\upsilon}(f^u)^{\upsilon}$, $\upsilon\in[0,1]$, which turns the interval system into a family of ordinary SDEs. Below every parameter means its value at a fixed $\upsilon$. Put $k=\min\{k_2,k_4\}$ and $M=k_1x_0/k$, and let

$$R_1=\frac{pk_3}{k_4}\Big(\frac{k_1x_0}{k_2}\Big)^{p},$$

the deterministic threshold. Assume (H): $M^p|\gamma(u)|\le\delta<1$ for all $u$.

**Theorem.**

1. *(Well-posedness.)* For every positive initial value there is a unique global solution, which stays positive almost surely.
2. *(Extinction.)* Let $\sigma'^2=\sigma^2+\int_{\mathbb Y}\frac{\gamma^2(u)}{(1+\delta)^2}\lambda(du)$, and start in $\Upsilon=\{x+y<M\}$. If $\sigma'^2>\frac{p^2k_3^2}{2k_4}$, then

$$\limsup_{t\to\infty}\frac{\ln y(t)}{t}\le\frac{p^2k_3^2}{2\sigma'^2}-k_4<0\quad\text{a.s.}$$

Suppose instead that $\sigma'^2\le pk_3/M^p$ and $\frac{pk_3}{k_4}M^p-\frac{\sigma'^2}{2k_4}M^{2p}<1$. Then

$$\limsup_{t\to\infty}\frac{\ln y(t)}{t}\le k_4\Big[\frac{pk_3}{k_4}M^p-\frac{\sigma'^2}{2k_4}M^{2p}-1\Big]<0\quad\text{a.s.}$$

In both cases the product species dies out exponentially fast.
3. *(Persistence in the mean.)* Let $\sigma''^2=\sigma^2+\int_{\mathbb Y}\frac{\gamma^2(u)}{(1-\delta)^2}\lambda(du)$. Suppose (L): $R_1^s:=R_1-\frac{\sigma''^2}{2k_4}M^{2p}>1$. Then

$$\liminf_{t\to\infty}\frac1t\int_0^ty(s)\,ds\ \ge\ \frac{k_1x_0}{k_4}-\frac{k_2}{k_4}\Big[\frac{k_4}{pk_3}+\frac{\sigma''^2}{2pk_3}M^{2p}\Big]^{1/p}>0\quad\text{a.s.}$$

So large noise, from Brownian or jump perturbations, can drive the reaction to extinction even when the deterministic model reacts. Persistence requires the stochastic threshold $R_1^s$, which is the deterministic $R_1$ reduced by a noise term, to exceed $1$.

## Expansion

The set $\Upsilon$ is invariant because $d(x+y)=(k_1x_0-k_2x-k_4y)\,dt\le(k_1x_0-k(x+y))\,dt$, and positivity follows from a Lyapunov function argument with stopping times. For extinction, apply Itô's formula for jump processes to $\ln y$. The drift is $pk_3x^p-k_4-\frac{\sigma^2}{2}x^{2p}$, plus a jump compensator bounded with (H) by $-\frac12\int\frac{\gamma^2}{(1+\delta)^2}\lambda(du)\,x^{2p}$. The function $z\mapsto pk_3z-\frac{\sigma'^2}{2}z^2$ of $z=x^p\in[0,M^p]$ is maximized either at $z=pk_3/\sigma'^2$ or at the endpoint $M^p$, which gives the two cases. The martingale terms are $o(t)$ by the strong law of large numbers for local martingales. For persistence, combine the same Itô expansion with the time-averaged identity obtained by integrating $dx+dy$, and use the lower bound that (L) provides. Varying $\upsilon\in[0,1]$ sweeps the thresholds over the whole interval of imprecise parameters.

These are the existence theorem (Section 3), the extinction theorem (Section 4) and the persistence theorem (Section 5) of the source.

## Sources

- F. Sun, "Dynamics of an imprecise stochastic multimolecular biochemical reaction model with Lévy jumps", arXiv:2004.14163 (2020). <https://doi.org/10.48550/arXiv.2004.14163>
