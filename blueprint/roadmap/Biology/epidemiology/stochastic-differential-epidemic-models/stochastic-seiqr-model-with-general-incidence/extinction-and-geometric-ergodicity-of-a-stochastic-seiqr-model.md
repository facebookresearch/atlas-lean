# Extinction and geometric ergodicity of a stochastic SEIQR model with general incidence

**Model.** Susceptible $S$, exposed $E$, infectious $I$, quarantined $Q$ and recovered $R$ individuals evolve under independent Brownian perturbations $B_1, \dots, B_5$:

$$\begin{aligned}
dS &= \big[b - \beta S\,h(I) - (\eta + \mu + d_3)S\big]dt + \sigma_1 S\,dB_1,\\
dE &= \big[\beta S\,h(I) - (\lambda + \mu + d_2)E\big]dt + \sigma_2 E\,dB_2,\\
dI &= \big[\lambda E - (\mu + \nu + \gamma + d_1)I\big]dt + \sigma_3 I\,dB_3,\\
dQ &= \big[d_3 S + d_2 E + d_1 I - (\mu + \tau)Q\big]dt + \sigma_4 Q\,dB_4,\\
dR &= \big[\eta S + \tau Q + \gamma I - \mu R\big]dt + \sigma_5 R\,dB_5,
\end{aligned}$$

with positive constants: recruitment $b$, transmission $\beta$, natural death $\mu$, vaccination $\eta$, quarantine rates $d_1, d_2, d_3$, latency exit $\lambda$, disease death $\nu$, recovery $\gamma$ and quarantine release $\tau$. The incidence $h$ is nonnegative and $C^2$ on $[0,\infty)$, with $h(0) = 0$, $h'(0) > 0$ and $h(I)/I$ non-increasing on $I > 0$, so that $h(I) \le h'(0)I$ (for instance $h(x) = x/(1 + 0.01x)$; $h(x) = x^2$ is excluded). Write $\tilde S_0 = b/(\eta + \mu + d_3)$ and $\sigma_{\max}^2 = \max_i \sigma_i^2$.

**Theorem.**
1. *Well-posedness.* For every initial value in $\mathbb{R}_+^5$ there is a unique global solution, which stays in $\mathbb{R}_+^5$ almost surely.
2. *Stochastic permanence.* The solution is stochastically ultimately bounded and stochastically permanent: for every $\epsilon \in (0,1)$ there are $0 < \kappa < \chi$ with $\limsup_t \mathbb{P}(\|X(t)\| > \chi) < \epsilon$ and $\liminf_t \mathbb{P}(\|X(t)\| \ge \kappa) \ge 1 - \epsilon$.
3. *Extinction.* If $\mu > \frac12\sigma_{\max}^2$ and $\sigma_2^2 \wedge \sigma_3^2 > 4\big(\beta h'(0)\tilde S_0 - \mu\big)$, then almost surely

$$\limsup_{t\to\infty}\frac{\ln\big(E(t) + I(t)\big)}{t} \le \beta h'(0)\tilde S_0 - \mu - \frac{\sigma_2^2 \wedge \sigma_3^2}{4} < 0,$$

and the time averages $\langle S\rangle_t \to \tilde S_0$, $\langle Q\rangle_t \to \dfrac{b\,d_3}{(\mu + \tau)(\eta + \mu + d_3)}$, $\langle R\rangle_t \to \dfrac{b\,[\eta(\mu + \tau) + \tau d_3]}{\mu(\eta + \mu + d_3)(\mu + \tau)}$ almost surely.
4. *Ergodicity.* The Markov process $X(t) = (S, E, I, Q, R)$ is $V$-geometrically ergodic: it has a unique stationary distribution $\pi$, and for some $C, \Lambda > 0$ and all measurable $g$ with $|g| \le V$, $|\mathbb{E}\,g(X(t)) - \pi(g)| \le C\,V(X_0)\,e^{-\Lambda t}$.

## Proof sketch

Positivity and global existence follow from a Lyapunov function of the form $\sum (x - 1 - \ln x)$ that cannot explode before an exit time. Permanence uses moment bounds from Young's and Chebyshev's inequalities. For extinction, Itô's formula applied to $\ln(E + I)$ the bound $h(I) \le h'(0)I$, and the comparison $S(t) \lesssim \tilde S_0$ (the disease-free level) give a growth rate bounded by the linearized force of infection $\beta h'(0)\tilde S_0$ minus mortality and a noise correction; the strong law for the martingale terms closes the argument. The source's statement of Theorem 5.1 (arXiv:2412.00405) prints the noise hypothesis as $\sigma_1^2 \wedge \sigma_3^2$; its proof uses $\sigma_2^2 \wedge \sigma_3^2$ throughout, which is the hypothesis that makes the stated rate negative, and is the one stated here. Geometric ergodicity follows from the Meyn–Tweedie criterion: a minorization condition on a compact set together with a drift condition $\mathcal{L}V \le \beta_1 - \beta_2 V$.

## Sources

- Brahim Boukanjime and Mohamed Maama, "Stochastic dynamics and probability analysis for a generalized epidemic model with environmental noise", *Chaos, Solitons & Fractals* 199 (2025), 116744, <https://doi.org/10.1016/j.chaos.2025.116744>. Preprint version: arXiv:2412.00405 (2024), model (Section 2), Theorem 3.1, Definitions 1–3 and Theorem 4.1, Lemma 1, Definition 4, Theorem 5.1 and Corollary 1, Lemma 2 and Theorem 6.1, <https://doi.org/10.48550/arXiv.2412.00405>.
