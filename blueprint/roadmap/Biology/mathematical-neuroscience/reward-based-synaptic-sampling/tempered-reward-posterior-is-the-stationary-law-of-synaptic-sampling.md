# Tempered reward posterior is the stationary law of synaptic sampling

**Setting.** A spiking network has synaptic parameters $\theta \in \mathbb{R}^{K}$ (one per potential synapse; a synapse is functional when its parameter is positive). Its performance is the expected discounted reward
$$V(\theta) = \Big\langle \int_0^\infty e^{-\tau/\tau_e}\, r(\tau)\, d\tau \Big\rangle_{p(r \mid \theta)} > 0,$$
where the expectation is over reward sequences produced by stochastic inputs, neuronal responses and reward delivery. Introduce a binary "goal reached" variable $v_b$ with likelihood $p_N(v_b = 1 \mid \theta) = V(\theta)/Z_V$, a structural prior $p_S(\theta)$, and the posterior $p^\ast(\theta \mid v_b = 1) \propto p_S(\theta)\, V(\theta)$. For temperature $T > 0$ the **tempered posterior** is
$$p_T^\ast(\theta) = \frac{1}{Z}\, p^\ast(\theta \mid v_b = 1)^{1/T}.$$
**Synaptic sampling** is the Itô diffusion, for each $i$,
$$d\theta_i = \beta\Big( \frac{\partial}{\partial \theta_i} \log p_S(\theta) + \frac{\partial}{\partial\theta_i} \log V(\theta) \Big) dt + \sqrt{2\beta T}\, dW_i ,$$
with learning rate $\beta > 0$ and independent Wiener processes $W_i$.

**Theorem.** If $p^\ast(\theta \mid v_b = 1)$ is a strictly positive probability density that is twice continuously differentiable in $\theta$, then $p_T^\ast$ is invariant under synaptic sampling, and it is the unique stationary distribution of the associated Fokker–Planck equation
$$\frac{\partial p_{FP}}{\partial t} = \sum_i \Big[ -\frac{\partial}{\partial\theta_i}\Big( \beta\, \frac{\partial}{\partial\theta_i}\log p^\ast(\theta\mid v_b=1)\; p_{FP} \Big) + \frac{\partial^2}{\partial\theta_i^2}\big( \beta T\, p_{FP} \big) \Big].$$

## Expansion

Write $\phi = \log p^\ast(\theta \mid v_b = 1)$. Substituting $p_{FP} = p_T^\ast = Z^{-1} e^{\phi/T}$, the diffusion term becomes $\partial_i(\beta T\, \partial_i p_T^\ast) = \partial_i(\beta T\, p_T^\ast\, \partial_i \phi / T) = \partial_i(\beta\, p_T^\ast\, \partial_i\phi)$, which cancels the drift term exactly, so the probability current vanishes and $\partial_t p_{FP} = 0$. Uniqueness follows because the noise is non-degenerate ($\beta T > 0$), so the process is ergodic: every region of parameter space is reachable from every other. Consequently the connectome never settles: after burn-in, synapses keep forming and retracting while the time spent in each configuration is proportional to its tempered posterior probability; $T < 1$ concentrates on high-reward configurations and $T > 1$ flattens them. The reward-gradient term is estimated online by synaptic eligibility traces $\dot e_i = -e_i/\tau_e + w_i\, y_{\mathrm{pre}_i}(z_{\mathrm{post}_i} - f_{\mathrm{post}_i})$ gated by reward, a policy-gradient estimator whose eligibility time constant equals the discount time constant $\tau_e$.

## Sources

- D. Kappel, R. Legenstein, S. Habenschuss, M. Hsieh and W. Maass, "A dynamic connectome supports the emergence of stable computational function of neural circuits through reward-based learning", eNeuro 5 (2018), ENEURO.0301-17.2018, Materials and Methods (Eqs. (6)–(11), Theorem 1, Eq. (15)), <https://doi.org/10.1523/ENEURO.0301-17.2018>, PMCID: PMC5913731.
- C. W. Gardiner, *Handbook of Stochastic Methods*, 3rd ed., Springer (2004), Section 3.7.
