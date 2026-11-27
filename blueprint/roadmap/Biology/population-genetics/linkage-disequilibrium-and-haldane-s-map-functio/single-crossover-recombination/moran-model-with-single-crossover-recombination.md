# Moran model with single-crossover recombination

Use the sites, links and recombinators of the [closed-form solution](closed-form-solution-of-continuous-time-single-crossover-recombination.md). In the **Moran model with single-crossover recombination** a population of fixed size $N$ is a counting vector $Z_t = (Z_t(x))_{x\in X}$ with $\sum_x Z_t(x) = N$, evolving as a continuous-time Markov chain with two independent kinds of transitions:

- **resampling:** $z \to z + \delta_x - \delta_y$ at rate $\frac{b}{2N} z(x) z(y)$, for types $x,y$;
- **recombination:** $z \to z + \delta_{(x_{<\alpha},y_{>\alpha})} + \delta_{(y_{<\alpha},x_{>\alpha})} - \delta_x - \delta_y$ at rate $\frac{\varrho_\alpha}{2N} z(x) z(y)$, for types $x,y$ and $\alpha \in L$.

**Theorem (Baake, Theorem 4).** Without resampling ($b = 0$) and with $Z_0$ fixed, the expectation solves the deterministic recombination equation:

$$\frac{d}{dt} E(Z_t) = \sum_{\alpha\in L} \varrho_\alpha \big( R_\alpha(E(Z_t)) - E(Z_t) \big),$$

hence $E(Z_t) = \varphi_t(Z_0) = \sum_{G\subseteq L} a_G(t) R_G(Z_0)$ for all $t \ge 0$, and likewise $E(T_G Z_t) = T_G(\varphi_t(Z_0))$ for the linkage disequilibrium operators $T_G$.

So in finite populations without drift, the expected type counts and expected disequilibria follow the infinite-population solution exactly, for every $N$, even though the dynamics is nonlinear.

**Proposition (Baake, Proposition 6; law of large numbers).** With resampling at any rate $b \ge 0$, let $\widehat Z^{(N)}_t = Z^{(N)}_t / N$ and suppose $\widehat Z^{(N)}_0 \to p_0$. Then for every $t \ge 0$,

$$\lim_{N\to\infty} \sup_{s \le t} \big| \widehat Z^{(N)}_s - p_s \big| = 0 \quad \text{almost surely},$$

where $p_s = \varphi_s(p_0)$ is the solution of the deterministic recombination equation.

## Depends on

- [Closed-form solution of continuous-time single-crossover recombination](closed-form-solution-of-continuous-time-single-crossover-recombination.md)

## Expansion

For general nonlinear dynamics $\frac{d}{dt}E(Z_t) = E(\Phi(Z_t))$ differs from $\Phi(E(Z_t))$. Here the recombinator $R_\alpha(Z_t)$ is a product of the marginals of $Z_t$ before and after $\alpha$, and without resampling the marginal processes on site sets that share no internal link are conditionally independent Markov chains given $Z_0$ (Lemma 5 of the paper), so the expectation of the product factorizes into the product of expectations. The law of large numbers is Kurtz's theorem for density-dependent Markov chains: the drift of $\widehat Z^{(N)}$ is the recombination vector field (resampling contributes no drift) and the jump sizes are $O(1/N)$.

## Sources

- E. Baake, *Deterministic and stochastic aspects of single-crossover recombination*, in *Proceedings of the International Congress of Mathematicians 2010 (ICM 2010)*, Vol. IV (2011), 3037–3053, <https://doi.org/10.1142/9789814324359_0178>; preprint arXiv:1101.2081, <https://doi.org/10.48550/arXiv.1101.2081>.
