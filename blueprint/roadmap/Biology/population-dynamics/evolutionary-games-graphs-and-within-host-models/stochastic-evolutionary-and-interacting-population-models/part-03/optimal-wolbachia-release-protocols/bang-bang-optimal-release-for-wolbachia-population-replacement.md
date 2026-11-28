# Bang-bang optimal release for Wolbachia population replacement

**Model.** Let $n_1$ be the density of wild (uninfected) mosquitoes and $n_2$ that of *Wolbachia*-infected mosquitoes, released at rate $u(t) \ge 0$:

$$\dot n_1 = b_1 n_1\Bigl(1 - s_h\frac{n_2}{n_1+n_2}\Bigr)\Bigl(1 - \frac{n_1+n_2}{K}\Bigr) - d_1 n_1, \qquad \dot n_2 = b_2 n_2\Bigl(1 - \frac{n_1+n_2}{K}\Bigr) - d_2 n_2 + u,$$

with cytoplasmic-incompatibility rate $s_h \in (0,1]$, carrying capacity $K$, and initial state $(n_1^*, 0)$ (wild equilibrium, no infection). Admissible releases are

$$\mathcal U_{T,C,M} = \Bigl\{u \in L^\infty(0,T) : 0 \le u \le M \text{ a.e.},\ \int_0^T u\,dt \le C\Bigr\}$$

(total stock $C$, maximal release flux $M$), and the cost is $J(u) = \tfrac12 n_1(T)^2 + \tfrac12\bigl[(n_2^* - n_2(T))_+\bigr]^2$.

**High-fecundity limit.** Set $b_i = b_i^0/\varepsilon$. As $\varepsilon \to 0$ the total population is slaved to $K$, and the infection frequency $p = n_2/(n_1+n_2)$ converges uniformly to the solution of

$$\dot p = f(p) + u\,g(p), \qquad p(0) = 0,$$

$$f(p) = p(1-p)\,\frac{d_1b_2^0 - d_2b_1^0(1 - s_hp)}{b_1^0(1-p)(1-s_hp) + b_2^0p}, \qquad g(p) = \frac1K\,\frac{b_1^0(1-p)(1-s_hp)}{b_1^0(1-p)(1-s_hp) + b_2^0p}.$$

Assume $1 - s_h < \frac{d_1b_2^0}{d_2b_1^0} < 1$ (condition (6) of the source, under which a coexistence equilibrium exists). Then $f$ is bistable with invasion threshold $\theta = \frac1{s_h}\bigl(1 - \frac{d_1b_2^0}{d_2b_1^0}\bigr) \in (0,1)$. The costs $J^\varepsilon$ $\Gamma$-converge to $J^0(u) = K^2(1-p(T))^2$. Minimizers of the full problem converge strongly in $L^1(0,T)$, up to subsequences, to minimizers of $\inf_{u\in\mathcal U_{T,C,M}}(1-p(T))^2$.

**Theorem (reduced problem).** Assume $T > C/M$. Every optimal release uses the whole stock, $\int_0^T u = C$, and is bang-bang ($u \in \{0, M\}$ a.e.). If $M \le \max_{p\in[0,\theta]}(-f(p)/g(p))$, the unique optimum is $u^* = M\mathbb 1_{[T-C/M,\,T]}$. Otherwise, with

$$C^*(M) = \int_0^{\theta}\frac{M\,dp}{f(p) + M g(p)},$$

1. if $C < C^*(M)$, the unique optimum is $u^* = M\mathbb 1_{[T-C/M,\,T]}$ (release everything at the end), and $p(T) < \theta$;
2. if $C > C^*(M)$, the unique optimum is $u^* = M\mathbb 1_{[0,\,C/M]}$ (release everything at the start), and $p(T) > \theta$;
3. if $C = C^*(M)$, every $u^*_\lambda = M\mathbb 1_{[\lambda,\lambda + C/M]}$ with $\lambda \in [0, T - C/M]$ is optimal, with $p(T) = \theta$.

So the optimal protocol is a single full-rate release phase. It jumps from the end to the start of the window exactly when the stock suffices to push the infection frequency over the bistability threshold $\theta$.

## Expansion

$C^*(M)$ is the stock consumed by releasing at full rate $M$ from $p = 0$ until $p$ reaches $\theta$, since $dt = dp/(f + Mg)$. Above $\theta$, $f > 0$, so the frequency keeps increasing without releases and it pays to cross $\theta$ as early as possible. Below $\theta$, $f < 0$, so released infection decays and releases should be postponed to the end. Pontryagin's principle gives a switching function $\lambda(t)g(p(t))$ compared with a constant multiplier for the stock constraint. The monotonicity of $f/g$ on $(0,\theta)$ excludes singular arcs and more than one switch, which leaves only the two extreme single-interval controls.

## Sources

- Luís Almeida, Yannick Privat, Martin Strugarek, Nicolas Vauchelet, "Optimal releases for population replacement strategies, application to Wolbachia", arXiv (2019). Section 2 (model, admissible set, Proposition 1 on the slow–fast limit, reduced frequency equation), Section 3: Proposition 2, Theorem 1, Corollary 1. <https://doi.org/10.48550/arXiv.1909.02727>. Published version: SIAM Journal on Mathematical Analysis 51(4) (2019), 3170–3194, <https://doi.org/10.1137/18m1189841>; locators above refer to the arXiv version.
