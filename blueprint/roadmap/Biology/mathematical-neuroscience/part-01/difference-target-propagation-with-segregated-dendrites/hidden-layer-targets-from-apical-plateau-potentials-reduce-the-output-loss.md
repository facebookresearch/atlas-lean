# Hidden-layer targets from apical plateau potentials reduce the output loss

**Setting.** A network has a hidden layer of three-compartment neurons (soma, basal dendrites receiving feedforward input, and apical dendrites receiving feedback through fixed random weights $Y$) and an output layer of two-compartment neurons receiving the hidden spikes through weights $W^1$ with biases $b^1$. Learning alternates a **forward phase** (input only) and a **target phase** (output neurons additionally driven by a teaching current). Write $\bar\phi^{0f}$ for the time-averaged hidden firing rates in the forward phase, $\bar\phi^{1f}, \bar\phi^{1t}$ for the output rates in the two phases, and set the output target $\phi^{1*} = \bar\phi^{1t}$. Let $\sigma$ be a differentiable sigmoid, $\phi_{\max}$ the maximal rate, $k_d$ a dendrite-to-soma gain, and

$$\beta(u) = \phi_{\max}\,\sigma\big(k_d(W^1u + b^1)\big), \qquad \gamma(u) = \sigma(Yu),$$

the forward map from hidden rates to output rates and the feedback map from output rates to apical plateau potentials.

The **plateau potentials** $\alpha^f, \alpha^t$ are $\sigma$ of the apical voltage averaged at the end of each phase; the model uses the hidden targets $\phi^{0*} = \bar\phi^{0f} + \alpha^t - \alpha^f$ and local losses

$$L^1 \approx \|\bar\phi^{1t} - \bar\phi^{1f}\|_2^2, \qquad L^0 \approx \|\phi^{0*} - \bar\phi^{0f}\|_2^2 = \|\alpha^t - \alpha^f\|_2^2,$$

which approximate the difference-target-propagation target

$$\tilde\phi^{0*} = \bar\phi^{0f} + \gamma(\bar\phi^{1t}) - \gamma\big(\beta(\bar\phi^{0f})\big).$$

**Theorem.** Let $e = \phi^{1*} - \beta(\bar\phi^{0f})$ and let $J_\beta, J_\gamma$ be the Jacobians of $\beta$ at $\bar\phi^{0f}$ and of $\gamma$ at $\beta(\bar\phi^{0f})$. If the largest eigenvalue $\mu$ of $(I - J_\beta J_\gamma)^{\top}(I - J_\beta J_\gamma)$ is less than $1$ and $\|e\|$ is sufficiently small, then

$$\big\|\phi^{1*} - \beta(\tilde\phi^{0*})\big\|_2^2 \ \le\ \|e\|_2^2 ,$$

with strict inequality when $e \neq 0$: moving the hidden layer to its target moves the output closer to its target.

**Lemma (rates from filtered spikes).** Let the spike times on $[t_0, t_1]$, $\Delta t = t_1 - t_0$, form an inhomogeneous Poisson process, and filter the train by the synaptic kernel $\kappa(t) = \big(e^{-t/\tau_L} - e^{-t/\tau_s}\big)\Theta(t)/(\tau_L - \tau_s)$, with $\Theta$ the Heaviside step. Then the expected window average $\mathbb E[\bar s]$ of the filtered train is at most the window-averaged rate $\bar\phi$, and close to it for $\Delta t \gg \tau_L, \tau_s$. Together with the assumption $\bar V^{1f} \approx k_d\bar V^{1bf}$ of the source's Theorem 1 (Eq. 26), where $\bar V^{1f}$ and $\bar V^{1bf}$ are the time-averaged somatic and basal voltages of the output units in the forward phase, this justifies replacing the expected output drive $\phi_{\max}\sigma(\mathbb E[\bar V^{1f}])$ by $\beta(\bar\phi^{0f})$, since then $\mathbb E[\bar V^{1f}] \approx k_d\big(W^1\,\mathbb E[\bar s^{0f}] + b^1\big) \approx k_d(W^1\bar\phi^{0f} + b^1)$. (The source's proof writes $\beta(u) = \phi_{\max}\sigma(k_dW^1u)$, i.e. sets $b^1 = 0$; the bias changes neither the form of $J_\beta$ nor the Theorem.)

## Expansion

By Taylor expansion, $\tilde\phi^{0*} = \bar\phi^{0f} + J_\gamma e + o(\|e\|)$, and then $\beta(\tilde\phi^{0*}) = \beta(\bar\phi^{0f}) + J_\beta J_\gamma e + o(\|e\|)$, so $\phi^{1*} - \beta(\tilde\phi^{0*}) = (I - J_\beta J_\gamma)e + o(\|e\|)$. Its squared norm is at most $\mu\|e\|^2 + o(\|e\|^2)$, which is below $\|e\|^2$ once the remainder is smaller than $(1-\mu)\|e\|^2$. The condition on $\mu$ is not guaranteed a priori; in simulations the feedforward weights come to satisfy it during the first training epoch, much as feedforward weights align with fixed random feedback in feedback alignment. Since $\alpha^f \approx \gamma(\bar\phi^{1f}) \approx \gamma(\beta(\bar\phi^{0f}))$ and $\alpha^t \approx \gamma(\bar\phi^{1t})$ in the linear regime of $\sigma$, the plateau-based target $\phi^{0*}$ approximates $\tilde\phi^{0*}$ using only quantities local to each hidden neuron.

## Sources

- J. Guerguiev, T. P. Lillicrap, B. A. Richards, "Towards deep learning with segregated dendrites", eLife (2017), Results Eqs. (5)–(10), Materials and methods Eqs. (21)–(43), Materials and methods: Proofs (Theorem 1 and its proof) and Lemma for firing rates (Lemma 1), <https://doi.org/10.7554/eLife.22901>, PMCID PMC5716677.
