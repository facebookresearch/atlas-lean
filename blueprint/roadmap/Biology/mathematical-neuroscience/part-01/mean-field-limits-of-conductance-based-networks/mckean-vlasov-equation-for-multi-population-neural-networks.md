# McKean–Vlasov equation for multi-population neural networks

**Network.** Neurons are split into $P$ populations; population $\alpha$ has $N_\alpha$ neurons with $N_\alpha / N \to \lambda_\alpha \in (0, 1)$. Neuron $i$ in population $\alpha = p(i)$ has state $X^{i,N}_t \in \mathbb{R}^d$ (membrane potential, gating or recovery variables, synaptic variables; $d = 3$ for FitzHugh–Nagumo with one synaptic variable, $d = 5$ for Hodgkin–Huxley) and obeys

$$dX^{i,N}_t = f_\alpha(t, X^{i,N}_t)\,dt + \sum_{\gamma=1}^P \frac{1}{N_\gamma} \sum_{j:\,p(j) = \gamma} b_{\alpha\gamma}(X^{i,N}_t, X^{j,N}_t)\,dt + g_\alpha(t, X^{i,N}_t)\,dW^i_t + \sum_{\gamma=1}^P \frac{1}{N_\gamma} \sum_{j:\,p(j)=\gamma} \beta_{\alpha\gamma}(X^{i,N}_t, X^{j,N}_t)\,dB^{i\gamma}_t,$$

with independent Brownian motions $W^i$ ($m$-dimensional, intrinsic and external current noise) and $B^{i\gamma}$ ($\delta$-dimensional, noise on maximal synaptic conductances). For chemical synapses $b_{\alpha\gamma}(x, y)$ has first component $-\bar J_{\alpha\gamma}(V^x - V^{\mathrm{rev}}_{\alpha\gamma})\,y^{\mathrm{syn}}$, the conductance-weighted drive by the presynaptic synaptic variable.

**Hypotheses.** For all $\alpha, \gamma$:

- (H1) $f_\alpha, g_\alpha$ are locally Lipschitz in $x$, uniformly in $t \in [0, T]$;
- (H2) $b_{\alpha\gamma}, \beta_{\alpha\gamma}$ are locally Lipschitz;
- (H3) $\max\big(\|b_{\alpha\gamma}(x,z)\|^2, \|\beta_{\alpha\gamma}(x,z)\|^2\big) \le \tilde K(1 + \|x\|^2)$;
- (H4) $x^{\mathsf T} f_\alpha(t, x) + \tfrac12 \|g_\alpha(t, x)\|^2 \le K(1 + \|x\|^2)$ (monotone growth; the cubic FitzHugh–Nagumo drift is only locally Lipschitz but satisfies it).

**Mean-field equation.** With $\bar Z$ an independent copy of $\bar X$ with the same law $m_t$,

$$d\bar X^\alpha_t = f_\alpha(t, \bar X^\alpha_t)\,dt + \sum_{\gamma} \mathbb E_{\bar Z}\big[b_{\alpha\gamma}(\bar X^\alpha_t, \bar Z^\gamma_t)\big]dt + g_\alpha(t, \bar X^\alpha_t)\,dW^\alpha_t + \sum_\gamma \mathbb E_{\bar Z}\big[\beta_{\alpha\gamma}(\bar X^\alpha_t, \bar Z^\gamma_t)\big]dB^{\alpha\gamma}_t, \quad \alpha = 1, \dots, P.$$

The densities $p_\alpha(t, z)$ of $\bar X^\alpha_t$ solve the nonlocal McKean–Vlasov–Fokker–Planck system

$$\partial_t p_\alpha = -\operatorname{div}_z\!\Big(\big(f_\alpha(t,z) + \textstyle\sum_\gamma \int b_{\alpha\gamma}(z, y)\, p_\gamma(t, y)\,dy\big)\, p_\alpha\Big) + \tfrac12 \sum_{i,j} \partial^2_{z_i z_j}\big(D^\alpha_{ij}(z)\, p_\alpha\big),$$

with $D^\alpha(z) = \sum_\gamma \mathbb E_Z[\beta_{\alpha\gamma}(z, Z)]\,\mathbb E_Z[\beta_{\alpha\gamma}(z,Z)]^{\mathsf T} + g_\alpha g_\alpha^{\mathsf T}(t, z)$.

**Theorem (well-posedness).** Under (H1)–(H4), for any $T > 0$ and square-integrable initial condition, the mean-field equation has a unique solution on $[0, T]$, and it has bounded second moments.

## Depends on

- [The FitzHugh–Nagumo vector field](../../fitzhugh-nagumo-model/field.md)
- [The Hodgkin–Huxley vector field](../../hodgkin-huxley-model/field.md)

## Expansion

First, (H3)–(H4) and Itô's formula applied to $\|\bar X_t\|^2$ with Gronwall's lemma give an a priori bound $\mathbb E[\sup_{s \le t}\|\bar X_s\|^2] < \infty$ for any solution. Existence: define the map $\Phi$ sending a process $X$ to the solution $Y$ of the linear-in-law SDE in which the expectations are taken under the law of $X$; iterate $X^{k+1} = \Phi(X^k)$. On the event that paths stay in a ball of radius $U$, (H1)–(H2) make the drift and diffusion Lipschitz, and Cauchy–Schwarz plus the Burkholder–Davis–Gundy inequality give $\mathbb E[\sup_{s\le t}\|X^{k+1}_s - X^k_s\|^2] \le C_U \int_0^t \mathbb E[\sup_{r \le s}\|X^k_r - X^{k-1}_r\|^2]\,ds$, hence factorial convergence up to the exit time $\tau_U$. The moment bound shows $\tau_U \to \infty$ almost surely as $U \to \infty$, giving a global solution; uniqueness follows from the same estimate and Gronwall's lemma.

## Sources

- J. Baladron, D. Fasoli, O. Faugeras, J. Touboul, "Mean-field description and propagation of chaos in networks of Hodgkin–Huxley and FitzHugh–Nagumo neurons", *The Journal of Mathematical Neuroscience* 2 (2012) 10. Section 2.5 (network equations, Eqs. 18–19; hypotheses (H1)–(H4), Eq. 20), Section 3.1 (network equation, Eq. 21; mean-field equation, Eqs. 22–23; McKean–Vlasov–Fokker–Planck equation, Eq. 24), Lemma 3 and Theorem 2. <https://doi.org/10.1186/2190-8567-2-10>. PMCID: PMC3497713.
