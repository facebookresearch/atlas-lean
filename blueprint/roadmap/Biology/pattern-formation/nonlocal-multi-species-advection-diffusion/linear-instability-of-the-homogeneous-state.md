# Linear instability of the homogeneous state of nonlocal multi-species advection–diffusion

On the flat torus $\mathbb T = \prod_{h=1}^n [0, L_h]$ (periodic boundary conditions) consider $N$ species with densities
$u_i(x,t) > 0$ moving by diffusion and nonlocal advection:

$$\frac{\partial u_i}{\partial t} = D_i \Delta u_i + \nabla \cdot \Bigl( u_i \sum_{j=1}^N \gamma_{ij} \nabla (K * u_j) \Bigr), \qquad i = 1, \dots, N,$$

where $D_i > 0$, $\gamma_{ij} \in \mathbb{R}$ ($\gamma_{ij} > 0$: species $i$ moves away from $j$; $\gamma_{ij} < 0$: towards $j$), and the
detection kernel $K$ is symmetric ($K(x) = K(-x)$), non-negative, with $\|K\|_{L^1} = 1$. The masses $p_i = \int_{\mathbb T} u_i\,dx$ are
conserved, so $\bar u = (\bar u_1, \dots, \bar u_N)$, $\bar u_i = p_i/|\mathbb T|$, is a homogeneous steady state.

**Proposition (dispersion relation).** The admissible wave vectors are $\kappa = (2\pi q_1/L_1, \dots, 2\pi q_n/L_n)$ with $q = (q_1, \dots, q_n) \in \mathbb Z^n \setminus \{0\}$; the coordinates $q_h$ may have mixed signs, and $\kappa$ and $-\kappa$ give the same real modes, so it suffices to take one representative of each pair $\{q, -q\}$ (but not only $q \in \mathbb N^n$). Perturbations $u - \bar u = w\, e^{\lambda t + i\kappa\cdot x}$ satisfy to first order $\lambda(\kappa)\, w = |\kappa|^2 \mathcal L(\kappa)\, w$ with

$$\mathcal L(\kappa)_{ii} = -D_i - \gamma_{ii}\bar u_i \hat K(\kappa), \qquad \mathcal L(\kappa)_{ij} = -\gamma_{ij}\bar u_i \hat K(\kappa) \quad (i \ne j),$$

where $\hat K(\kappa) = \int_{\mathbb T} K(x) e^{-i\kappa\cdot x}\,dx$ is the Fourier coefficient of $K$, real and even in $\kappa$ because $K$ is even. The state $\bar u$ is linearly unstable iff some admissible $\kappa \ne 0$ gives
$\mathcal L(\kappa)$ an eigenvalue with positive real part. If $\gamma_{ij} = \gamma_{ji}$ and all $\bar u_i$ are equal, $\mathcal L(\kappa)$ is
symmetric and its eigenvalues are real.

**Two species.** For $N = 2$ the eigenvalues of $\mathcal L(\kappa)$ are

$$\lambda^\pm = \tfrac12\Bigl[ -(\gamma_{11}\bar u_1 + \gamma_{22}\bar u_2)\hat K - (D_1 + D_2) \pm \sqrt{\Delta} \Bigr],$$

$$\Delta = \bigl((\gamma_{11}\bar u_1 - \gamma_{22}\bar u_2)^2 + 4\gamma_{12}\gamma_{21}\bar u_1\bar u_2\bigr)\hat K^2 + 2(D_1 - D_2)(\gamma_{11}\bar u_1 - \gamma_{22}\bar u_2)\hat K + (D_1 - D_2)^2,$$

which are real when $\gamma_{12} = \gamma_{21}$. In the symmetric case $p_1 = p_2 = 1$, $L_h = 1$, $D_1 = D_2$, $\gamma_{11} = \gamma_{22}$,
$\gamma_{12} = \gamma_{21}$, the homogeneous state is linearly unstable iff for some admissible $\kappa \ne 0$

$$-\gamma_{11}\hat K(\kappa) + |\gamma_{12}\hat K(\kappa)| > D_1 .$$

## Expansion

Linearizing $\nabla\cdot(u_i \gamma_{ij}\nabla K * u_j)$ at $\bar u$ gives $\bar u_i \gamma_{ij}\Delta(K * w_j)$, whose Fourier symbol is
$-|\kappa|^2 \bar u_i \gamma_{ij}\hat K(\kappa)$, and diffusion contributes $-|\kappa|^2 D_i$. The factor $|\kappa|^2 > 0$ does not change signs of
eigenvalues. For $N=2$ the characteristic polynomial of $\mathcal L$ is quadratic with the stated roots; in the symmetric case the two
eigenvalues are $-D_1 - (\gamma_{11} \mp \gamma_{12})\bar u \hat K$, and the larger one is positive iff the displayed inequality holds.
(Giunta et al. 2022, Equations 1 and 4–14.)

## Sources

- V. Giunta, T. Hillen, M. A. Lewis, and J. R. Potts, "Detecting minimum energy states and multi-stability in nonlocal advection–diffusion models for interacting species", Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01824-1> (PMC9585017).
