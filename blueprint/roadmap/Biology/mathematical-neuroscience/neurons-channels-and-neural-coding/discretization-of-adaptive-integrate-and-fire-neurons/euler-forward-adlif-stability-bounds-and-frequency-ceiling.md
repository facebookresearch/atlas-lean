# Euler-forward discretization of the adaptive LIF neuron: shrinking stable frequency band

Consider the subthreshold adaptive LIF neuron $\tau_u \dot u = -u + I - w$, $\tau_w \dot w = -w + a u + b z$ with $\tau_u, \tau_w > 0$, and fix a time step $\Delta t > 0$ with $\alpha = e^{-\Delta t/\tau_u}$, $\beta = e^{-\Delta t/\tau_w}$, $\bar\alpha = 1-\alpha$, $\bar\beta = 1-\beta$. The Euler-forward (EF) scheme updates both variables from the previous state,

$$u[k] = \alpha u[k-1] + \bar\alpha\,(-w[k-1] + I[k]), \qquad w[k] = \beta w[k-1] + \bar\beta\,(a\,u[k-1] + b\,S[k]),$$

so without input and spikes $s[k] = \bar A_{EF}\, s[k-1]$ with

$$\bar A_{EF} = \begin{pmatrix} \alpha & -\bar\alpha \\ a\bar\beta & \beta \end{pmatrix}.$$

Let $a_0 = (\alpha-\beta)^2/(4\bar\alpha\bar\beta)$ and $a_{\max} = (1-\alpha\beta)/(\bar\alpha\bar\beta)$. Then:

1. For $a \in (a_0, a_{\max})$ the eigenvalues are complex, $\lambda_{1,2} = \frac{\alpha+\beta}{2} \pm \frac{i}{2}\sqrt{4a\bar\alpha\bar\beta - (\alpha-\beta)^2}$, with spectral radius $\sqrt{\alpha\beta + a\bar\alpha\bar\beta}$; the neuron oscillates and is asymptotically stable. For $a \in (-1, a_0]$ the eigenvalues are real and the neuron is stable without oscillating. Overall it is asymptotically stable exactly on $a \in (-1, a_{\max})$.
2. Unlike the continuous model, the coupling $a$ changes the decay rate: the modulus grows with $a$ and reaches $1$ at $a_{\max}$.
3. Because $\operatorname{Re}\lambda = (\alpha+\beta)/2 > 0$, every stable oscillating EF neuron has intrinsic frequency $f < f_N/2$, where $f_N = 1/(2\Delta t)$ is the Nyquist frequency.
4. The largest stable angle is $\varphi_{\max} = \arcsin\!\big(\tfrac12\sqrt{4 - (\alpha+\beta)^2}\big)$, which tends to $0$ as $\tau_u, \tau_w \to \infty$: for slow membranes the stable oscillation band of the EF neuron collapses.

## Expansion

The characteristic polynomial is $\lambda^2 - (\alpha+\beta)\lambda + \alpha\beta + a\bar\alpha\bar\beta$ with discriminant $(\alpha-\beta)^2 - 4a\bar\alpha\bar\beta$, negative exactly when $a > a_0$. In the complex regime the modulus is $\sqrt{\det} = \sqrt{\alpha\beta + a\bar\alpha\bar\beta}$, which is below $1$ iff $a < a_{\max}$. The real part of the eigenvalues does not depend on $a$, so as $a$ grows the eigenvalues climb a vertical line in the right half-plane and leave the unit disk; the argument therefore stays below $\pi/2$. At $a_{\max}$ the modulus is $1$ and $\operatorname{Im}\lambda = \frac12\sqrt{4 - (\alpha+\beta)^2}$, and $\alpha, \beta \to 1$ as the time constants grow. On the real side the larger root reaches $1$ at $a = -1$. These are Lemmas 1.3, 1.4, 1.7, 1.8 and Corollary 1.4.1 of the source; the contrast with the symplectic-Euler scheme, whose eigenvalue modulus does not depend on $a$, is the source's argument for using it in trained spiking networks.

## Sources

- M. Baronig, R. Ferrand, S. Sabathiel, R. Legenstein, Advancing spatio-temporal processing through adaptation in spiking neural networks, Nat. Commun. 16 (2025), 5776, Eqs. (6), (9), (26)–(45), (70), Lemmas 1.3, 1.4, 1.7, 1.8, Corollary 1.4.1. <https://doi.org/10.1038/s41467-025-60878-z> (PMCID: PMC12218304)
