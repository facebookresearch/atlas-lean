# Residual networks converge to their continuous-depth flow at rate $1/L$

Let $E$ be a real Banach space, let $g : \mathbb{R} \times E \to E$ be $C^2$ as a function of
$(t, z)$ and $K$-Lipschitz in $z$ for every $t \in [0, 1]$, and let $z_0 \in E$. Then the flow
$\dot z(t) = g(t, z(t))$, $z(0) = z_0$, exists on $[0, 1]$, and there is a constant $C$ such that
for every depth $L \ge 1$ the residual network

$$Z_0 = z_0, \qquad Z_{l+1} = Z_l + \frac1L\, g\Big(\frac lL, Z_l\Big) \quad (l = 0, \dots, L - 1)$$

satisfies $\lVert Z_L - z(1) \rVert \le C / L$.

The residual network with the $1/L$ scaling is the explicit Euler scheme with step $1/L$ for the
ODE, and the bound is the first-order convergence of Euler's method with $t_0 = 0$, $T = 1$,
$h = 1/L$. In the scaled residual networks of E, Ma, Wojtowytsch and Wu the block is
$g_l(z) = U_l \sigma(W_l z)$; the theorem applies when $U_l = U(l/L)$ and $W_l = W(l/L)$ for
smooth weight paths and a $C^2$ activation with bounded derivative (e.g. $\tanh$), which makes the
block globally Lipschitz in the state as the theorem requires. A $C^2$ activation alone is not
enough: $\sigma(s) = s^2$ with $U = W = 1$ gives $\dot z = z^2$, whose solution from $z_0 = 1$ blows
up at $t = 1$. The theorem does not cover the ReLU, which is not $C^2$.

## Sources

- W. E, J. Han and Q. Li, *A mean-field optimal control formulation of deep learning*, Res. Math. Sci. 6 (2019), §3, equation (1) and its continuous-time idealisation.
- W. E, C. Ma, S. Wojtowytsch and L. Wu, *Towards a mathematical understanding of neural network-based machine learning: what we know and what we don't*, CSIAM Trans. Appl. Math. (2020), §3.3 (scaled residual networks and their ODE limit).
