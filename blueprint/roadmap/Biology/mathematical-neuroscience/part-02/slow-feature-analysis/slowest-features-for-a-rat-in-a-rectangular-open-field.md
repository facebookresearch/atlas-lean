# Slowest features for a rat in a rectangular open field

Take the configuration space $V = [0, L_x] \times [0, L_y] \times S^1$ with coordinates $(x, y, \phi)$ for position and head direction, uniform configuration density $p_s$, and velocity moments independent of configuration and decorrelated across directions:

$$K = \operatorname{diag}\big(\langle v_x^2\rangle, \langle v_y^2\rangle, \langle \omega^2\rangle\big), \qquad \langle v_x^2\rangle = \langle v_y^2\rangle,$$

where $v_x, v_y$ are translational and $\omega$ rotational velocities. Then the slowness operator of [Delta-optimal functions as eigenfunctions of the slowness operator](delta-optimal-functions-as-eigenfunctions-of-the-slowness-operator.md) is $-\big(\langle v_x^2\rangle \partial_x^2 + \langle v_y^2\rangle \partial_y^2 + \langle\omega^2\rangle \partial_\phi^2\big)$ with Neumann conditions on the walls and periodicity in $\phi$.

**Proposition.** The eigenfunctions are, up to normalization,

$$g_{lmn}(x, y, \phi) = \cos\!\Big(\frac{l\pi x}{L_x}\Big)\cos\!\Big(\frac{m\pi y}{L_y}\Big) \times \begin{cases}\cos(n\phi) \\ \sin(n\phi)\end{cases}, \qquad l, m, n \in \mathbb{Z}_{\ge 0},\ (l,m,n) \ne (0,0,0),$$

with $\Delta$-values

$$\Delta_{lmn} = \langle v_x^2\rangle \Big(\frac{l\pi}{L_x}\Big)^2 + \langle v_y^2\rangle \Big(\frac{m\pi}{L_y}\Big)^2 + \langle\omega^2\rangle\, n^2 .$$

Consequently, if rotation is fast relative to translation (relative rotational speed $\gg 1$), the slowest features have $n = 0$: they are invariant to head direction and code for position on a rectangular cosine grid, and a subsequent sparse (ICA) stage yields localized place-cell-like units. If rotation is slow relative to translation, the slowest features have $l = m = 0$: they are invariant to position and form a Fourier basis in head direction, the analogue of head-direction cells.

## Depends on

- [Delta-optimal functions as eigenfunctions of the slowness operator](delta-optimal-functions-as-eigenfunctions-of-the-slowness-operator.md)

## Expansion

With constant $p_s$ and $K$ the operator separates, and the Neumann Laplacian on an interval of length $L$ has eigenfunctions $\cos(l\pi x/L)$ with eigenvalues $(l\pi/L)^2$; on the circle the eigenfunctions are $\cos(n\phi), \sin(n\phi)$ with eigenvalues $n^2$. Ordering the $\Delta_{lmn}$ selects which modes are slowest. The excluded index $(0,0,0)$ is the constant function, which violates the unit-variance constraint. The simulations of a hierarchical SFA network trained on visual input from a virtual rat reproduce these predicted modes up to sign, mirroring and mixing of nearly degenerate modes.

## Sources

- M. Franzius, H. Sprekeler, L. Wiskott, "Slowness and sparseness lead to place, head-direction, and spatial-view cells", PLoS Computational Biology 3(8) (2007) e166, Methods, open-field analysis following Theorem 5 and Figure 3, <https://doi.org/10.1371/journal.pcbi.0030166>, PMCID PMC1963505.
