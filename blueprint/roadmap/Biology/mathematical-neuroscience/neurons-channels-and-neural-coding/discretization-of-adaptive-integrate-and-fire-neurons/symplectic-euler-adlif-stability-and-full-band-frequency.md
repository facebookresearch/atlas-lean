# Symplectic-Euler discretization of the adaptive LIF neuron: stability at every intrinsic frequency

The adaptive leaky integrate-and-fire (adLIF) neuron has membrane potential $u$ and adaptation current $w$ obeying, below threshold,

$$\tau_u \dot u = -u + I(t) - w, \qquad \tau_w \dot w = -w + a\,u + b\,z(t),$$

with $\tau_u, \tau_w > 0$, coupling $a \in \mathbb{R}$, spike-triggered adaptation $b \ge 0$ and output spike train $z$. Without input the continuous system is Lyapunov stable for all $a \ge -1$.

Fix a time step $\Delta t > 0$ and put $\alpha = e^{-\Delta t/\tau_u}$, $\beta = e^{-\Delta t/\tau_w}$, $\bar\alpha = 1-\alpha$, $\bar\beta = 1-\beta$. The symplectic-Euler (SE) scheme updates $u$ first and then computes $w[k]$ from the new $u[k]$:

$$u[k] = \alpha u[k-1] + \bar\alpha\,(-w[k-1] + I[k]), \qquad w[k] = \beta w[k-1] + \bar\beta\,(a\,u[k] + b\,S[k]).$$

Below threshold ($S \equiv 0$, no input) this is $s[k] = \bar A_{SE}\, s[k-1]$ with

$$\bar A_{SE} = \begin{pmatrix} \alpha & -\bar\alpha \\ a\bar\beta\alpha & \beta - a\bar\beta\bar\alpha \end{pmatrix}, \qquad \det \bar A_{SE} = \alpha\beta .$$

Let $a_1 = (\sqrt\beta - \sqrt\alpha)^2/(\bar\alpha\bar\beta)$, $a_2 = (\sqrt\beta + \sqrt\alpha)^2/(\bar\alpha\bar\beta)$ and $a_{\max} = (1+\alpha)(1+\beta)/(\bar\alpha\bar\beta)$. Then:

1. For $a \in (a_1, a_2)$ the eigenvalues are complex conjugate with modulus $r = \sqrt{\alpha\beta} < 1$, independent of $a$: the neuron oscillates and decays at the same rate as the continuous model.
2. For $a \in (-1, a_1] \cup [a_2, a_{\max})$ the eigenvalues are real and the neuron is asymptotically stable without oscillating; it is asymptotically stable for all $a \in (-1, a_{\max})$ and unstable for $a < -1$ or $a > a_{\max}$.
3. (Full-band frequency coverage.) Let $f_N = 1/(2\Delta t)$ be the Nyquist frequency and define the intrinsic frequency $f = \varphi/(2\pi\Delta t)$ from the argument $\varphi \in [0, \pi]$ of the upper eigenvalue. For every $\tau_u, \tau_w > 0$ the map $a \mapsto f$ is a bijection from $[a_1, a_2]$ onto $[0, f_N]$; every such neuron is asymptotically stable with decay rate $\sqrt{\alpha\beta} < 1$.

## Expansion

The characteristic polynomial is $\lambda^2 - (\alpha + \beta - a\bar\alpha\bar\beta)\lambda + \alpha\beta$. Its discriminant vanishes when $a\bar\alpha\bar\beta = (\sqrt\alpha \pm \sqrt\beta)^2$, giving $a_1, a_2$; between them the roots are complex and their common modulus is $\sqrt{\det} = \sqrt{\alpha\beta}$. On the real side, the root crosses $+1$ exactly at $a = -1$ and $-1$ exactly at $a = a_{\max}$. For the frequency map, $\operatorname{Re}\lambda = (\alpha + \beta - a\bar\alpha\bar\beta)/2$ is strictly decreasing in $a$, so $\cos\varphi = \operatorname{Re}\lambda/\sqrt{\alpha\beta}$ decreases continuously from $1$ at $a_1$ to $-1$ at $a_2$, and $\varphi = \arccos(\cdot)$ sweeps $[0, \pi]$. Because $a$ moves only the angle and not the modulus of the eigenvalues, trained frequencies can never push the neuron out of the stable region, in contrast with the Euler-forward scheme. These are Lemma 1.2 (continuous stability), Lemmas 1.5 and 1.6, Corollary 1.6.1 and Theorem 1.1 of the source.

## Sources

- M. Baronig, R. Ferrand, S. Sabathiel, R. Legenstein, Advancing spatio-temporal processing through adaptation in spiking neural networks, Nat. Commun. 16 (2025), 5776, Eqs. (2), (3), (10), (11), Lemmas 1.2, 1.5, 1.6, Corollary 1.6.1, Theorem 1.1. <https://doi.org/10.1038/s41467-025-60878-z> (PMCID: PMC12218304)
