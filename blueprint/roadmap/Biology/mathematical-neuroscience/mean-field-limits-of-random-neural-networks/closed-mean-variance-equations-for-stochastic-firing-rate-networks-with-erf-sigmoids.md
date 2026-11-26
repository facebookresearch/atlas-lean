# Closed mean–variance equations for stochastic firing-rate networks with erf sigmoids

**Network.** $P$ populations of firing-rate neurons; the potential of neuron $i$ in population $\alpha$ obeys
$$dV_i = \Big(-\frac{V_i}{\tau_\alpha} + \sum_{\beta=1}^P\sum_{j=1}^{N_\beta}J_{ij}S_\beta(V_j) + I_\alpha(t)\Big)dt + f_\alpha\,dW_i,$$
with independent Brownian motions $W_i$, sigmoidal rate functions $S_\beta$, and independent Gaussian synaptic weights $J_{ij}$ of mean $\bar J_{\alpha\beta}/N_\beta$ and standard deviation $\sigma_{\alpha\beta}/\sqrt{N_\beta}$.

**Proposition (mean-field limit).** Under the local chaos hypothesis, as $N_\beta \to \infty$ the input $\sum_jJ_{ij}S_\beta(V_j)$ converges in law to a Gaussian process depending only on $(\alpha, \beta)$, and each neuron's potential converges to the solution of the non-Markovian equation
$$dV_\alpha = \Big(-\frac{V_\alpha}{\tau_\alpha} + \sum_\beta U^V_{\alpha\beta}(t) + I_\alpha(t)\Big)dt + f_\alpha\,dW^\alpha_t,$$
where $U^V_{\alpha\beta}$ is Gaussian with mean $\bar J_{\alpha\beta}\mathbb{E}[S_\beta(V_\beta(t))]$ and covariance $\sigma^2_{\alpha\beta}\mathbb{E}[S_\beta(V_\beta(t))S_\beta(V_\beta(s))]$. Gaussian initial data give Gaussian solutions, so the limit is determined by the mean $\mu_\alpha(t)$ and covariance $C_{\alpha\alpha}(t,s)$ (populations are uncorrelated):
$$\dot\mu_\alpha = -\frac{\mu_\alpha}{\tau_\alpha} + \sum_\beta\bar J_{\alpha\beta}\int_{\mathbb{R}}S_\beta\big(x\sqrt{v_\beta(t)} + \mu_\beta(t)\big)Dx + I_\alpha(t),$$
$$C_{\alpha\alpha}(t,s) = e^{-(t+s)/\tau_\alpha}\Big[\mathrm{Var}V_\alpha(0) + \frac{\tau_\alpha f_\alpha^2}{2}\big(e^{2s/\tau_\alpha} - 1\big) + \sum_\beta\sigma^2_{\alpha\beta}\int_0^t\!\!\int_0^s e^{(u+v)/\tau_\alpha}\Delta_{\alpha\beta}(u,v)\,du\,dv\Big],$$
for $s \le t$, where $v_\beta(t) = C_{\beta\beta}(t,t)$, $Dx$ is the standard Gaussian measure and $\Delta_{\alpha\beta}(u,v) = \mathbb{E}[S_\beta(V_\beta(u))S_\beta(V_\beta(v))]$ is a two-dimensional Gaussian integral.

**Erf closure.** If $S_\beta(x) = \Phi(g_\beta x + \gamma_\beta)$ with $\Phi$ the standard normal distribution function, the mean equation becomes explicit:
$$\dot\mu_\alpha = -\frac{\mu_\alpha}{\tau_\alpha} + \sum_\beta\bar J_{\alpha\beta}\,\Phi\Big(\frac{g_\beta\mu_\beta + \gamma_\beta}{\sqrt{1 + g_\beta^2v_\beta}}\Big) + I_\alpha(t),$$
so noise and connectivity disorder enter the deterministic rate equation as an effective, variance-dependent flattening of the gain.

## Expansion

The Gaussian identity $\int\Phi(g(x\sqrt v + \mu) + \gamma)\,Dx = \Phi\big((g\mu + \gamma)/\sqrt{1 + g^2v}\big)$ follows by writing $\Phi(z) = \Pr(\xi \le z)$ for an independent standard normal $\xi$ and noting $\xi - g\sqrt v\,x \sim N(0, 1 + g^2v)$. Because the effective gain $g/\sqrt{1 + g^2v}$ shrinks as variance grows, increasing intrinsic noise $f_\alpha$ or synaptic disorder $\sigma_{\alpha\beta}$ can move, create or destroy stationary states and suppress or induce oscillations in excitatory–inhibitory networks, effects absent from the classical Wilson–Cowan firing-rate equations obtained when the variance terms are dropped.

## Sources

- Jonathan Touboul, Bard Ermentrout, Olivier Faugeras and Bruno Cessac, "Stochastic firing rate models", arXiv:1001.3872 (2010), Section 2 (mean-field convergence propositions and moment equations, analysis with erf firing-rate functions) and Appendix B, <https://doi.org/10.48550/arXiv.1001.3872>.
