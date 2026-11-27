# Threshold and stability of the infected equilibrium

**Model.** Viral load $V \ge 0$ and effector T cells $T > 0$ obey

$$\dot V = pV\Big(1 - \frac{V}{K}\Big) - c_T V T - cV, \qquad \dot T = s_T + r\,T\,G(V) - \delta_T T,$$

with replication rate $p$, carrying capacity $K$, non-immune clearance $c$, T-cell killing rate $c_T$, homeostatic supply $s_T$ and decay $\delta_T$ (so the uninfected T-cell level is $T_0 = s_T/\delta_T$), maximal activation rate $r$, and a bounded activation function with $G(0) = 0$ and $G'(V) > 0$ for $V > 0$ (for example the Hill function $G(V) = V^m/(V^m + k_T^m)$). All parameters are positive.

**Theorem.** Let

$$\lambda = p - c - c_T T_0 .$$

1. *(Virus-free equilibrium.)* $E_0 = (0, T_0)$ has Jacobian eigenvalues $-\delta_T$ and $\lambda$: it is a locally asymptotically stable node for $\lambda < 0$ (degenerate when $\lambda = -\delta_T$), non-hyperbolic at $\lambda = 0$, and a saddle for $\lambda > 0$.
2. *(Infected equilibrium.)* An equilibrium $E^\ast = (V^\ast, T^\ast)$ with $V^\ast > 0$ exists if and only if $p > c$ and $\lambda > 0$, and it is then unique, with

    $$T^\ast = \frac{p\,\big(V_{\max} - V^\ast\big)}{c_T K}, \qquad V_{\max} = \frac{(p - c)K}{p},$$

    where $V^\ast$ is the unique root in $\big(0,\ V_{\max} - c_T T_0 K/p\big)$ of $G(V) = G_0(V) := \frac{\delta_T}{r}\Big(1 - \frac{c_T T_0 K}{p\,(V_{\max} - V)}\Big)$.
    3. *(Stability.)* Whenever $E^\ast$ exists it is locally asymptotically stable: the trace of $J(E^\ast)$ is $-\big(pV^\ast/K + s_T/T^\ast\big) < 0$ and its determinant is $p s_T V^\ast/(K T^\ast) + c_T r V^\ast T^\ast G'(V^\ast) > 0$; it is a node or a spiral according to the sign of the discriminant.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)

## Expansion

At $V = 0$ the Jacobian is triangular, with entries $p - c - c_T T_0 = \lambda$ and $rG(0) - \delta_T = -\delta_T$, which gives item 1; the discriminant $(\lambda + \delta_T)^2 \ge 0$ rules out spirals. At a positive equilibrium the $V$-equation gives $T^\ast$ linearly in $V^\ast$, positive iff $V^\ast < V_{\max}$, which requires $p > c$; substituting into the $T$-equation gives $G(V^\ast) = G_0(V^\ast)$. Since $G_0$ strictly decreases on $(0, V_{\max})$ and $G$ strictly increases from $G(0) = 0$, the difference $G_0 - G$ is strictly decreasing and has a root iff $G_0(0) > 0$, i.e. iff $p - c > c_T T_0$, i.e. $\lambda > 0$; the root lies below the zero of $G_0$, which is $V_{\max} - c_T T_0 K/p$. Using the equilibrium equations the Jacobian at $E^\ast$ simplifies to $\begin{pmatrix} -pV^\ast/K & -c_T V^\ast \\ r T^\ast G'(V^\ast) & -s_T/T^\ast \end{pmatrix}$, whose trace is negative and determinant positive. The threshold $\lambda = 0$ is a transcritical bifurcation: viral replication net of non-immune clearance must exceed the killing capacity of the resting T-cell pool, $\lambda > 0$ being the analogue of a within-host reproduction number $p/(c + c_T T_0) > 1$; near $\lambda = 0$ the equilibrium viral load is very sensitive to parameters.

## Sources

- A. E. S. Almocera, G. Quiroz and E. A. Hernandez-Vargas, "Stability analysis in COVID-19 within-host model with immune response", Communications in Nonlinear Science and Numerical Simulation 95 (2021), 105584, Section 2 (Eqs. (1)–(18), Theorems 1–3, Lemmas 1–3), <https://doi.org/10.1016/j.cnsns.2020.105584>, PMCID: PMC7606083.
