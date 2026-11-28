# Two-cell instability of the homogeneous Hes1 state

**Reduced model.** After quasi-steady-state reduction of a five-variable Hes1/Notch/Delta/Ngn2 cell model, each cell carries a Hes1-type variable $x$ and a Delta-type signal $y$, coupled to neighbours through the mean incoming signal $\langle y_{\mathrm{in}}\rangle$:

$$\dot x = \frac{\langle y_{\mathrm{in}}\rangle}{a + x^k} - x =: \langle y_{\mathrm{in}}\rangle f(x) - x, \qquad \dot y = v\Bigl(\frac{1}{1 + bx^h} - y\Bigr) =: v\bigl(g(x) - y\bigr),$$

with $a, b, v > 0$ and Hill exponents $k, h \ge 1$. Neighbour signal activates $x$ (Notch activation of Hes1), and $x$ represses the cell's own signal (Hes1 repression of Delta via Ngn2).

**Proposition (homogeneous state).** The homogeneous problem has a unique stationary point $\bar x_0 \in (0,1)$, which is also the unique homogeneous steady state of the full five-variable system.

**Proposition (two-cell instability).** For two cells coupled to each other with periodic boundary conditions, the homogeneous stationary solution of the reduced system is unstable iff

$$f(\bar x_0)\,g'(\bar x_0) - f'(\bar x_0)\,g(\bar x_0) < -1 .$$

When this holds, small differences between the cells grow into an alternating high/low Hes1 pattern (lateral inhibition), the mechanism behind salt-and-pepper fate decisions in the neural tube.

## Expansion

At the homogeneous state $\bar y = g(\bar x_0)$ and $\bar y f(\bar x_0) = \bar x_0$. Linearizing the two-cell system and splitting into the in-phase mode (both cells equal) and the anti-phase mode (opposite perturbations), the in-phase block is always stable, while the anti-phase block $\begin{pmatrix}\bar y f'(\bar x_0) - 1 & -f(\bar x_0)\\ v g'(\bar x_0) & -v\end{pmatrix}$ has negative trace and determinant $v\bigl(1 - \bar y f'(\bar x_0) + f(\bar x_0)g'(\bar x_0)\bigr)$; using $\bar y = g(\bar x_0)$ the determinant becomes negative, giving a real positive eigenvalue, exactly when $f g' - f' g < -1$. Since $f' < 0$, the term $-gf'$ is positive, so the inequality needs $fg'$ strongly negative, i.e. steep repression of the signal.

## Sources

- G. Menz, S. Engblom, "Modelling Population-Level Hes1 Dynamics: Insights from a Multi-Framework Approach", *Bulletin of Mathematical Biology* 87(6) (2025), 74, reduced system (type 1) in Section 3 and the two propositions of the stability appendix, <https://doi.org/10.1007/s11538-025-01447-9> (preprint arXiv:2411.09721).
