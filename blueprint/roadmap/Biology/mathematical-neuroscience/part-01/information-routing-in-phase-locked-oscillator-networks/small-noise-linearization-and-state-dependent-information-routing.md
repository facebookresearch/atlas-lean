# Small-noise linearization of phase-locked oscillator networks and state-dependent routing direction

**Phase model.** Consider $N$ weakly coupled noisy limit-cycle oscillators reduced to phases,

$$\dot\varphi_i = \omega_i + \sum_{j} \gamma_{i,j}(\varphi_i - \varphi_j) + \varsigma_i \, \xi_i(t), \qquad i = 1, \dots, N,$$

with smooth $2\pi$-periodic coupling functions $\gamma_{i,j}$ and independent Gaussian white noises $\xi_i$. Let the noise-free system have a phase-locked solution $\varphi_i^{\mathrm{ref}}(t) = \Omega t + \phi_i$ with constant offsets $\Delta\phi_{i,j} = \phi_i - \phi_j$ and common frequency $\Omega = \omega_i + \sum_k \gamma_{i,k}(\Delta\phi_{i,k})$.

**Statement 1 (linearization).** To first order in the noise, the fluctuations $\psi_i = \varphi_i - \varphi_i^{\mathrm{ref}}$ obey coupled Ornstein–Uhlenbeck equations

$$d\psi_i = -\sum_{j \ne i} g_{i,j}\, (\psi_i - \psi_j)\, dt + \varsigma_i \, dW_i, \qquad g_{i,j} = -\gamma_{i,j}'(\Delta\phi_{i,j}),$$

i.e. the effective interaction is a weighted graph Laplacian whose weights depend on the collective reference state, not only on the physical coupling.

**Statement 2 (two units).** For $N = 2$ put $a = g_{1,2}$, $b = g_{2,1}$, $u = \psi_1 - \psi_2$ and, if $a + b \ne 0$, $s = (b\psi_1 + a\psi_2)/(a + b)$. Then

$$du = -(a + b)\, u\, dt + \varsigma_1 dW_1 - \varsigma_2 dW_2, \qquad ds = \frac{b\, \varsigma_1 dW_1 + a\, \varsigma_2 dW_2}{a + b}.$$

(a) The locked state is linearly stable iff $a + b > 0$; then $u$ has stationary variance $(\varsigma_1^2 + \varsigma_2^2)/(2(a + b))$.
(b) A phase kick $\delta$ given to unit 2 at time $0$ produces $\psi_1(t) = \frac{a\delta}{a+b}\big(1 - e^{-(a+b)t}\big)$ and $\psi_2(t) = \frac{a\delta}{a+b} + \frac{b\delta}{a+b} e^{-(a+b)t}$; symmetrically for unit 1 with $a \leftrightarrow b$. Thus if $a \gg b > 0$, input to unit 2 is retained by the collective phase and copied to unit 1 after a delay of order $1/(a+b)$, while input to unit 1 is erased: information is routed from 2 to 1.
(c) For two identical, symmetrically coupled units ($\gamma_{1,2} = \gamma_{2,1} = \gamma$), $\Delta = \varphi_1 - \varphi_2$ obeys $\dot\Delta = 2\gamma_{\mathrm{odd}}(\Delta)$ with $\gamma_{\mathrm{odd}}(x) = \tfrac12(\gamma(x) - \gamma(-x))$; the stable locked states are zeros of $\gamma_{\mathrm{odd}}$ with negative slope, and $a = -\gamma'(\Delta^*)$, $b = -\gamma'(-\Delta^*)$. Since $\gamma_{\mathrm{odd}}'$ is even, $-\Delta^*$ is also a stable locked state, in which $a$ and $b$ are exchanged. A symmetry-broken locked state ($\Delta^* \notin \{0, \pi\}$) therefore produces anisotropic routing, and switching between the two states reverses the routing direction with no change of the physical network.

## Expansion

Statement 1 is the first-order expansion of $\gamma_{i,j}(\Delta\phi_{i,j} + \psi_i - \psi_j)$. In Statement 2 the change of variables decouples the system: $u$ is an OU process with rate $a+b$, and $s$ has zero drift because $b\cdot(-a u) + a\cdot(b u) = 0$. Inverting, $\psi_1 = s + \frac{a}{a+b}u$ and $\psi_2 = s - \frac{b}{a+b}u$; a kick $\delta$ on unit 2 shifts $s$ by $a\delta/(a+b)$ and $u$ by $-\delta$, after which $u$ relaxes exponentially, which gives (b). For (c), $a + b = -(\gamma'(\Delta^*) + \gamma'(-\Delta^*)) = -2\gamma_{\mathrm{odd}}'(\Delta^*)$, so stability is the negative-slope condition. In the source, two Wilson–Cowan neural masses have two such locked states, and the predicted delayed mutual information and transfer entropy curves reverse their asymmetry between them; the direction of routing is set by which unit is weakly coupled in the current state (the lagging unit can push the leading one), not by the order of phase locking. For modular networks a second, collective phase reduction gives equations of the same form for module phases, so routing between modules can be switched by local changes inside one module.

## Depends on

- [Delayed mutual information of phase signals under a von Mises ansatz](delayed-mutual-information-of-phase-signals-under-a-von-mises-ansatz.md)

## Sources

- C. Kirst, M. Timme, D. Battaglia, "Dynamic information routing in complex networks", Nature Communications 7 (2016), 11061, Results ("Multi-stable dynamics and anisotropic information routing", Eqs. (3), (5), Fig. 2; "Information routing in networks of networks", Eq. (6)) and Methods ("Analytic derivation of the dMI and dTE curves", Eq. (9)), <https://doi.org/10.1038/ncomms11061> (PMC4832059).
