# Stability bound for a delayed visco-elastic model with substrate friction

**Model.** A cell or tissue segment of apparent length $l(t)$ is modeled as a standard solid: an elastic branch of stiffness $k_1 > 0$ relative to the reference length $l_0$, in parallel with a visco-elastic branch of stiffness $k_2 > 0$ whose rest-length $L(t)$ remodels toward the current length with rate $\gamma > 0$ after a delay $\tau \ge 0$ (the lag between chemical signalling and mechanical remodelling), with viscous friction $\eta \ge 0$ against the substrate. With linear strains,

$$-\eta\,\dot l(t) = k_1\big(l(t) - l_0\big) + k_2\big(l(t) - L(t)\big), \qquad \dot L(t) = \gamma\big(l(t-\tau) - L(t-\tau)\big), \qquad t > 0,$$

with constant history $l = l_0$, $L = L_0$ on $[-\tau, 0]$. Equivalently $\dot{\mathcal{L}} + \mathbf{A}\mathcal{L}(t) + \mathbf{B}\mathcal{L}(t-\tau) + \mathbf{c} = 0$ for $\mathcal{L} = (l, L)^T$, with

$$\mathbf{A} = \begin{pmatrix} (k_1 + k_2)/\eta & -k_2/\eta \\ 0 & 0 \end{pmatrix}, \qquad \mathbf{B} = \begin{pmatrix} 0 & 0 \\ -\gamma & \gamma \end{pmatrix}, \qquad \mathbf{c} = \begin{pmatrix} k_1 l_0/\eta \\ 0 \end{pmatrix}.$$

**Proposition.** The solution of this delay system is stable whenever

$$k_1 + k_2 - \gamma\eta - k_1\gamma\tau > 0.$$

In particular, larger delays $\tau$ and remodelling rates $\gamma$ (through the product $\gamma\tau$) are destabilizing, and so, perhaps counter-intuitively, is larger friction $\eta$ with the substrate.

## Expansion

Perturbations $e^{\lambda t}$ about the equilibrium satisfy $\det(\lambda I + \mathbf{A} + \mathbf{B}e^{-\lambda\tau}) = 0$, i.e.

$$\eta\lambda^2 + (k_1 + k_2)\lambda + \gamma e^{-\lambda\tau}(\eta\lambda + k_1) = 0.$$

Stability requires all roots in the open left half-plane. Splitting the characteristic function on the imaginary axis $\lambda = i\omega$ into real and imaginary parts $R(\omega)$ and $S(\omega)$, a Stépán-type root-counting criterion applies, and replacing $S$ by a polynomial lower bound $S^-(\omega) > 0$ on $(0,\infty)$ yields the explicit sufficient condition. Numerically computed stability borders in the parameter planes $(k_1,k_2)$, $(k_1,\eta)$, $(k_2,\eta)$ and $(\tau,\gamma)$ agree with the bound in shape, and with nonlinear strain measures the model produces sustained oscillations alternating between stable and unstable regions, as seen in remodelling, migrating and embryonic cells.

## Sources

- M. A. Dawi and J. J. Muñoz, "Stability bounds of a delay visco-elastic rheological model with substrate friction", arXiv:2101.07372 (2021), Section 2 (model), Section 3.1 (characteristic equation, analytical bounds and Proposition 1), Section 4 (nonlinear strain model), <https://doi.org/10.48550/arXiv.2101.07372>.
