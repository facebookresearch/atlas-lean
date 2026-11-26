# Optimal harvesting and seeding with bounded rates

**Model.** $d$ interacting species in a random environment follow $d\xi = b(\xi)\,dt + \sigma(\xi)\,dw$ on $\overline{S} = [0,\infty)^d$, with $b(0) = \sigma(0) = 0$ (extinct species stay extinct without intervention). Harvesting $Y(t)$ and seeding (repopulation) $Z(t)$, nondecreasing adapted processes, give

$$X(t) = x + \int_0^t b(X)\,ds + \int_0^t\sigma(X)\,dw - Y(t) + Z(t), \qquad X(t) \ge 0.$$

With prices $f_i$ and seeding costs $g_i$ (continuous, non-increasing, $f_i < g_i$) and discount $\delta > 0$, the value is

$$V(x) = \sup_{(Y,Z)}\ \mathbb{E}_x\Big[\int_0^\infty e^{-\delta s}f(X(s-))\cdot dY(s) - \int_0^\infty e^{-\delta s}g(X(s-))\cdot dZ(s)\Big].$$

Three regimes are considered: bounded seeding rate $dZ = C\,dt$, $0 \le C \le \lambda$, with unbounded harvesting; bounded seeding and harvesting rates $dY = R\,dt$, $0 \le R \le \mu$; and unbounded seeding with bounded harvesting.

**Theorem.**

*(1)* (Truncation, bounded seeding) If for some $U > 0$, $\sum_i[b_i(x) - \delta(x_i - U)]f_i < 0$ for $|x| > U$, then there is $x^* \in [0,U]^d$ with $V(x) = V(x^*) + f\cdot(x - x^*)$ outside $[0,U]^d$, and $V$ equals the value $V^U$ of the problem confined to $[0,U]^d$: above a threshold one harvests instantly down to $[0,U]^d$.

*(2)* (HJB, both rates bounded) $V$ is finite and continuous on $\overline{S}$ and is a viscosity solution of

$$(\mathcal{L} - \delta)V + \max_{\xi\in[-\lambda,\mu]}\big[\xi^-\cdot(f - \nabla V) - \xi^+\cdot(g - \nabla V)\big] = 0,$$

where $\mathcal{L}$ is the generator of the uncontrolled diffusion.

*(3)* (Numerical approximation) Under a diagonal-dominance condition on the diffusion matrix $\sigma\sigma'$, the values $V^h$ of locally consistent controlled Markov chains with step $h$ converge to $V$ (resp. $V^U$) on $[0,U]^d$ in each of the three regimes, and near-optimal chain policies are near-optimal for the diffusion.

## Expansion

When harvesting is unbounded and prices are fixed, harvesting a marginal unit is worth $f$, so outside the region where the drift can still pay off, the value function is affine with slope $f$; this reduces an unbounded problem to a box. Bounded rates turn the singular-control quasi-variational inequality into an ordinary HJB equation with a bounded control set, for which the dynamic programming principle yields viscosity sub- and supersolution properties. The Markov chain approximation method (Kushner-Dupuis) discretizes space with step $h$, chooses transition probabilities matching the drift and diffusion to first order, and its value converges by weak-convergence arguments; this makes multi-species harvesting problems computable.

## Sources

- Alexandru Hening and Ky Tran, "Harvesting and seeding of stochastic populations: analysis and numerical approximation", arXiv:1911.00734 (2019), Section 2, Proposition 2.3 and Theorems 2.5-2.8, <https://doi.org/10.48550/arXiv.1911.00734>.
