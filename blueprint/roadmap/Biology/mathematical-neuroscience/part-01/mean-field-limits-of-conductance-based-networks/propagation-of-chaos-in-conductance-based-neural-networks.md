# Propagation of chaos in conductance-based neural networks

**Setting.** Let $R^{i,N} = (V^i, q^i, y^i)$, $i = 1, \dots, N$, be the states of the multi-population conductance-based network (FitzHugh–Nagumo or Hodgkin–Huxley neurons with chemical synapses) of [McKean–Vlasov equation for multi-population neural networks](mckean-vlasov-equation-for-multi-population-neural-networks.md), with white-noise or Cox–Ingersoll–Ross maximal conductances, and assume hypotheses (A1)–(A4) there. Let the population sizes be $N_\gamma = c_\gamma N$ with fixed proportions $c_\gamma \in (0, 1)$. For each $i$ with $p(i) = \alpha$, let $\tilde R^i$ solve the mean-field equation of population $\alpha$ with the Brownian motions and initial condition of neuron $i$; the $\tilde R^i$ are independent, and $\tilde R^i$ has the law $m^\alpha$ of the unique mean-field solution of population $\alpha$.

**Theorem.** Under (A1)–(A4) there is a constant $C$, independent of $N$, such that for every choice of one neuron $i_\alpha$ in each population $\alpha$,

$$\sqrt N\;\mathbb E\Big[\sup_{t \le T} \sum_{\alpha} \big\|R^{i_\alpha,N}_t - \tilde R^{i_\alpha}_t\big\|^2\Big] \le C .$$

Consequently, as $N \to \infty$:

1. **Convergence.** For each neuron $i$ of population $\alpha$, the law of the process $(R^{i,N}_t)_{t \le T}$ converges to $m^\alpha$.
2. **Propagation of chaos.** For every fixed $k \ge 1$ and $k$-tuple of distinct neurons $(i_1, \dots, i_k)$, the law of $(R^{i_1,N}_t, \dots, R^{i_k,N}_t)_{t \le T}$ converges to the product $m^{p(i_1)} \otimes \cdots \otimes m^{p(i_k)}$: in the limit, any finite group of neurons behaves as independent copies of the mean-field processes of their populations.

The rate $N^{-1/2}$ for the mean squared distance is slower than the rate $N^{-1}$ of the globally Lipschitz case. The classical Hodgkin–Huxley drift does not satisfy (A3); the source states that the result extends to it by adding standard localisation arguments, without writing them out. Particle (Euler–Maruyama with $N$ samples) and Fokker–Planck simulations of a single FitzHugh–Nagumo population agree.

## Depends on

- [McKean–Vlasov equation for multi-population neural networks](mckean-vlasov-equation-for-multi-population-neural-networks.md)

## Expansion

The proof is by synchronous coupling (Sznitman's method), written for the Cox–Ingersoll–Ross model and adapted directly to the white-noise one; $\tilde R^i$ and $R^{i,N}$ share their conductance processes $J^{i\gamma}$. The interaction term $-\sum_\gamma (v - \bar V_{\alpha\gamma})\,j\,\frac{1}{N_\gamma}\sum_{j':\,p(j')=\gamma} y^{j'}$ is not globally Lipschitz, but $J^{i\gamma} > 0$ and $y^{j'} \in [0, 1]$ make it mean reverting in $V$. So Itô's formula for $(V^i)^{2q}$, stopped at the exit times of balls, bounds the moments of every order of $V^i$ and $\tilde V^i$, using the one-sided Lipschitz drift and the moments of the Cox–Ingersoll–Ross processes. Because the drift is polynomial, expectations are taken only after a pathwise bound on $\|R^{i,N}_t - \tilde R^i_t\|^2$ and on the squared difference $(\delta \bar y_t)^2$ of the empirical synaptic averages, which lies in $[0, 1]$. The fluctuation of $\frac{1}{N_\gamma}\sum_{j'} \tilde y^{j'}_t$ around $\mathbb E[y^\gamma_t]$, an average of independent bounded variables, has second moment $O(1/N)$. Gronwall's lemma then gives $\mathbb E[(\delta \bar y_t)^2] \le C/N$, the bound on $\frac1N\sum_i \mathbb E\|R^{i,N}_t - \tilde R^i_t\|^2$, and by exchangeability within populations the stated estimate. Convergence in $L^2$ of each coordinate to independent limits gives both convergence of the marginal laws and asymptotic independence of finite tuples.

## Sources

- M. Bossy, O. Faugeras, D. Talay, "Clarification and complement to 'Mean-field description and propagation of chaos in networks of Hodgkin–Huxley and FitzHugh–Nagumo neurons'", *The Journal of Mathematical Neuroscience* 5 (2015) 19. Section 2 (Hypothesis 2.1), Section 4 (Proposition 4.3, Remark 4.4, Proposition 4.5 with Eqs. 17–18 and its proof). <https://doi.org/10.1186/s13408-015-0031-8>. PMCID: PMC4556725.
- J. Baladron, D. Fasoli, O. Faugeras, J. Touboul, "Mean-field description and propagation of chaos in networks of Hodgkin–Huxley and FitzHugh–Nagumo neurons", *The Journal of Mathematical Neuroscience* 2 (2012) 10. Section 4 (numerical comparison of network and mean-field solutions); its propagation-of-chaos theorem under general locally Lipschitz hypotheses is corrected by the first source. <https://doi.org/10.1186/2190-8567-2-10>. PMCID: PMC3497713.
