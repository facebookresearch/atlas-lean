# Critical climate speed for partially sedentary populations

**Model.** A population with discrete annual generations lives in a suitable habitat patch of length $L$ that shifts at climate speed $c$ per year. After growth $n \mapsto f(n)$, with $f(0) = 0$ and $f'(0) = R > 1$, a fraction $p \in (0,1]$ disperses with a symmetric kernel $k$ and the rest stays put; individuals outside the patch die:

$$n_{t+1}(x) = \int_{-L/2 + ct}^{L/2 + ct} p\,f(n_t(y))\,k(x - y)\,dy + (1 - p)\,f(n_t(x)), \qquad x \in [-L/2 + c(t+1),\ L/2 + c(t+1)].$$

In the moving frame, persistence is decided by the dominant eigenvalue $\lambda$ of the linearized problem

$$\lambda\,u(x) = \int_{-L/2}^{L/2} pR\,u(y)\,k(x - y + c)\,dy + (1-p)R\,u(x + c)\ \ (x \in [-L/2, L/2]), \qquad u = 0 \text{ otherwise};$$

the population persists if $\lambda > 1$, and the **critical speed** $c^*$ solves $\lambda(c^*) = 1$.

**Lemma (top-hat kernel).** Let $k(x) = \frac{1}{4\beta}\chi_{[-2\beta, 2\beta]}(x)$ with $2\beta > L$ and $c < 2\beta - L$. Let $q = R(1-p)$ and $n(x) = \min\{n \ge 1 : x + nc \notin [-L/2, L/2]\}$. Then the eigenfunction is the step function

$$u(x) = \frac{B\,(\lambda^{n(x)} - q^{n(x)})}{\lambda^{n(x)}(\lambda - q)}, \qquad B = \frac{Rp}{4\beta}\int_{-L/2}^{L/2} u(y)\,dy,$$

with $\lceil L/c \rceil = N + 1$ steps. Writing $\epsilon = L/c - N$, the critical speed satisfies

$$c = \frac{4\beta\,(1 - q)}{pR\,\Big(N + \epsilon\,(1 - q^{N+1}) - \dfrac{q\,(1 - q^{N})}{1 - q}\Big)} .$$

## Expansion

With a top-hat kernel wider than the patch, every disperser lands uniformly, so the dispersal term is the constant $B$ and the eigenvalue problem collapses to the recursion $\lambda u(x) = B + q\,u(x + c)$, solved by summing a geometric series over the $n(x)$ years since location $x$ became suitable. Setting $\lambda = 1$ and integrating the steps (each of length $c$, the last of length $\epsilon c$) gives the transcendental equation for $c^*$, which has kinks at $c = L/N$ where a new step appears. Two regimes follow. If $c > L$, sedentary individuals are always left behind, so full dispersal ($p = 1$) persists at the highest speeds. If $c < L$, sedentary individuals near the trailing edge accumulate several years of growth, and a partially sedentary population can persist at higher climate speeds than a fully dispersing one, and usually has larger total size, because dispersal also wastes individuals that overshoot or land behind the habitat. Numerical results for the Laplace kernel and density-dependent dispersal agree.

## Sources

- C. A. Cobbold, R. Stana, "Should I stay or should I go: partially sedentary populations can outperform fully dispersing populations in response to climate-induced range shifts", Bulletin of Mathematical Biology (2020), model (2)–(4), travelling-pulse linearization (5)–(8), Lemma 1 (Eqs 9–12) and Appendix A, <https://doi.org/10.1007/s11538-020-00700-7>, PMCID PMC6994560.
