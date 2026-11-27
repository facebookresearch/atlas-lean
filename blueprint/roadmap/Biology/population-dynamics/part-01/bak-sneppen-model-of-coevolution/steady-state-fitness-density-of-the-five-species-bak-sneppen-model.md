# Steady-state fitness density of the five-species Bak–Sneppen model

**Model.** Five species on a cycle carry fitnesses $\vec f_k \in [0,1]^5$, initially i.i.d. uniform. At each step the species $\nu$ of minimal fitness and its two neighbors $\nu\pm1$ (indices mod $5$) receive fresh independent uniform fitnesses, the others are unchanged. The chain $(\vec f_k)$ is uniformly ergodic with absolutely continuous marginals of densities $g_k$ satisfying

$$g_{k+1}(\mathbf x) = \sum_{\nu=1}^5\int_{[0,1]^3}\mathbf 1\{\xi_2 < \min(\xi_1,\xi_3,\mathbf x_{]\nu[})\}\,g_k\big(\mathbf x_{]\nu[_{\boldsymbol\xi}}\big)\,d^3\boldsymbol\xi,$$

where $\mathbf x_{]\nu[}$ drops components $\nu,\nu\pm1$ and $\mathbf x_{]\nu[_{\boldsymbol\xi}}$ replaces them by $\boldsymbol\xi$; $g_k$ converges uniformly to the steady-state density $g$.

With $F_{n,m}(x) = {}_2F_1\big(\tfrac13(n + i\sqrt2), \tfrac13(n - i\sqrt2); \tfrac m3; x\big)$ (Gauss hypergeometric function), let

$$\mathcal G(x) = \tfrac32 F_{2,1}(1/2)\,F_{1,2}(x^3/2) + \tfrac98\,x\,F_{4,5}(1/2)\,F_{2,4}(x^3/2).$$

**Theorem.** The steady-state density is

$$g(\mathbf x) = \mathbf 1_{[0,1]^5}(\mathbf x)\sum_{\nu=1}^5 q\big(\min\{x_\nu,x_{\nu+1}\},\ \max\{x_\nu,x_{\nu+1}\}\big), \qquad q(x,y) = \mathcal G'(1-x)\,\mathcal B_1'(1-y) + B_{\circ,0}(x),$$

where $\mathcal B_1$ is the unique solution of the fifth-order linear ODE $\sum_{j=0}^5 c_j(y)\mathcal B_1^{(j)}(y) = 0$ with

$$\mathcal B_1(1) = \tfrac15,\quad \mathcal B_1'(1) = 0,\quad \mathcal B_1''(1) = -\tfrac15,\quad \mathcal B_1^{(3)}(1) = 1,\quad \mathcal B_1^{(4)}(1) = -\tfrac{18}{5},$$

whose coefficients are built from $\mathcal G$:

$$c_0 = \frac{18y^4}{(y^3+2)^2}\big[y(y^3-22)\mathcal G' + (5y^3-14)\mathcal G\big],\qquad c_1 = -y\,c_0,$$

$$c_2 = \frac{6}{y^3+2}\big[y(3y^6-38y^3-4)\mathcal G' + (15y^6-10y^3+4)\mathcal G\big],\qquad c_3 = -12y\big[y(4y^3-1)\mathcal G' + (5y^3+1)\mathcal G\big],$$

$$c_4 = -3y^2\big[y(y^3+2)\mathcal G' + (9y^3-2)\mathcal G\big],\qquad c_5 = y^3(y^3+2)\big[y\mathcal G' - \mathcal G\big],$$

and

$$B_{\circ,0}(x) = \int_{1-x}^1\frac1\xi\big[\mathcal G''(\xi)\mathcal B_1(\xi) - \mathcal G(\xi)\mathcal B_1''(\xi)\big]d\xi.$$

**Corollary.** At steady state the fitness of a randomly chosen species has density $g_{\mathrm{marg}}(x) = \big[\tfrac35 + \mathcal B_1'(1-x)\big]\mathbf 1_{[0,1]}(x)$.

## Expansion

The recursion preserves a finite-dimensional ansatz: $g_k$ is a sum over adjacent pairs of functions of the pair's minimum and maximum, written as polynomial expansions whose coefficients $\alpha_{i,j,k}$ satisfy explicit linear recursions (Proposition 1) and become constant for $k \ge i+j+1$ (Lemma 1). Passing to the limit turns the coefficient generating functions into solutions of linear ODEs; the cube $x^3$ and the factor $y^3+2$ reflect the three-site update and the five-site cycle, and the hypergeometric functions are the resulting special solutions. The question motivating such closed forms is whether, as the number of species grows, the marginal fitness becomes uniform on $[f_c,1]$ with $f_c \gtrapprox 2/3$.

## Sources

- Eckhard Schlemm, "A differential equation for the asymptotic fitness distribution in the Bak–Sneppen model with five species", arXiv (2015). Section 2 (formalization, Theorem 1, Corollary 1), Section 3 (Proposition 1, Lemma 1). <https://doi.org/10.48550/arXiv.1506.06238>. Published version: Mathematical Biosciences 267 (2015), 53–60, <https://doi.org/10.1016/j.mbs.2015.06.011>; locators above refer to the arXiv version.
