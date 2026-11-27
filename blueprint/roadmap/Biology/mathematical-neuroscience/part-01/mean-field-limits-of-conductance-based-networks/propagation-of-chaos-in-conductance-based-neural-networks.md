# Propagation of chaos in conductance-based neural networks

**Setting.** Let $X^{i,N}$ be the states of a multi-population network of stochastic conductance-based neurons (Hodgkin–Huxley or FitzHugh–Nagumo) with mean-field-scaled chemical-synapse interactions $b_{\alpha\gamma}$ and conductance noise $\beta_{\alpha\gamma}$, satisfying hypotheses (H1)–(H4), and let $\bar X^\alpha$ with law $m^\alpha$ be the unique solution of the population-$\alpha$ mean-field equation, all as in [McKean–Vlasov equation for multi-population neural networks](mckean-vlasov-equation-for-multi-population-neural-networks.md). Assume the initial conditions are independent, identically distributed within each population and square integrable, and $N_\alpha/N \to \lambda_\alpha \in (0,1)$.

**Theorem.** Under (H1)–(H4), as $N \to \infty$:

1. **Convergence.** For each neuron $i$ of population $\alpha$, the law of the process $(X^{i,N}_t)_{t \le T}$ converges to the law of $\bar X^\alpha$.
2. **Propagation of chaos.** For every fixed $k \ge 1$ and $k$-tuple of distinct neurons $(i_1, \dots, i_k)$, the law of $(X^{i_1,N}_t, \dots, X^{i_k,N}_t)_{t \le T}$ converges to the product $m^{p(i_1)} \otimes \cdots \otimes m^{p(i_k)}$: in the limit, any finite group of neurons behaves as independent copies of the mean-field processes of their populations.

Consequently correlations between pairs of neurons vanish as the network grows, and a population's activity is summarized by one nonlinear, law-dependent SDE (equivalently a Fokker–Planck equation) instead of $N$ coupled SDEs. Particle (Euler–Maruyama with $N$ samples) and Fokker–Planck simulations of a single FitzHugh–Nagumo population agree.

## Depends on

- [McKean–Vlasov equation for multi-population neural networks](mckean-vlasov-equation-for-multi-population-neural-networks.md)

## Expansion

The proof is by synchronous coupling (Sznitman's method). For each neuron $i$, build $\bar X^i$ solving the mean-field equation of population $p(i)$ driven by the same Brownian motions $W^i$, $B^{i\gamma}$ and the same initial condition as $X^{i,N}$; the $\bar X^i$ are independent. Subtract the two SDEs. The interaction difference splits into a term controlled by local Lipschitz continuity (H2) times $\|X^{j,N} - \bar X^j\|$, and a fluctuation term $\frac{1}{N_\gamma}\sum_j \big(b(\bar X^i, \bar X^j) - \mathbb E_{\bar Z}[b(\bar X^i, \bar Z)]\big)$, an average of conditionally centered, uncorrelated variables whose second moment is $O(1/N_\gamma)$ by (H3) and the moment bounds. Burkholder–Davis–Gundy and Gronwall, localized to balls where the coefficients are Lipschitz and de-localized using the moment bounds from (H4), give $\mathbb E[\sup_{t\le T}\|X^{i,N}_t - \bar X^i_t\|^2] \to 0$. Convergence in $L^2$ of each coordinate to independent limits yields both convergence of marginal laws and asymptotic independence of finite tuples.

## Sources

- J. Baladron, D. Fasoli, O. Faugeras, J. Touboul, "Mean-field description and propagation of chaos in networks of Hodgkin–Huxley and FitzHugh–Nagumo neurons", *The Journal of Mathematical Neuroscience* 2 (2012) 10. Section 3.2 (Theorem 4, proof in the Appendix) and Section 4 (numerical comparison of network and mean-field solutions). <https://doi.org/10.1186/2190-8567-2-10>. PMCID: PMC3497713.
