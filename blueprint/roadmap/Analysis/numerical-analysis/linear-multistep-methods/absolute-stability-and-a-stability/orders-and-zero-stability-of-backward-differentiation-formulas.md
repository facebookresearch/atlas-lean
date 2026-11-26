# Orders and zero-stability of the backward differentiation formulas

For $1 \le k \le 6$ the $k$-step [backward differentiation formula](backward-differentiation-formulas.md) has [order](../order-of-accuracy-and-error-constants.md) $k$, with the error constant $C_{k+1}$ below, and is zero-stable. For $k = 1, 2$ it is [A-stable](a-stability.md). For $3 \le k \le 6$ it is [stiffly stable](stiff-stability.md) with the constant $a$ below (and some $c > 0$) and [A(α)-stable](a-alpha-stability.md) with the angle $\alpha$ below. For $k \ge 7$ the backward differentiation formula of order $k$ is not zero-stable.

| $k$ | $C_{k+1}$ | $a$ in stiff stability | $\alpha$ in A(α)-stability |
|---|---|---|---|
| 1 | $-\tfrac12$ | A-stable | A-stable |
| 2 | $-\tfrac29$ | A-stable | A-stable |
| 3 | $-\tfrac3{22}$ | $0.1$ | $86^\circ$ |
| 4 | $-\tfrac{12}{125}$ | $0.7$ | $73^\circ$ |
| 5 | $-\tfrac{10}{137}$ | $2.4$ | $51^\circ$ |
| 6 | $-\tfrac{20}{343}$ | $6.1$ | $17^\circ$ |

The largest angles of A(α)-stability are $86.03^\circ$, $73.35^\circ$, $51.84^\circ$ and $17.84^\circ$ for $k = 3, \dots, 6$, rounded down here. The error constants are those of the normalization $\alpha_k = 1$; for $\sigma(1) = 1$ they are $C_{k+1}/\beta_k = -1/(k + 1)$.

## Depends on

- [Backward differentiation formulas](backward-differentiation-formulas.md)
- [Zero-stability](../zero-stability.md)
- [Stiff stability](stiff-stability.md)
- [A(α)-stability](a-alpha-stability.md)
- [Order of accuracy and error constants of a linear multistep method](../order-of-accuracy-and-error-constants.md)
- [A-stability](a-stability.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.2, Table 3 (coefficients, order, error constant and stability parameters for $k = 1, \dots, 6$) and the statement after it that for $p \ge 7$ these methods are not zero-stable. The angles $88^\circ$, $52^\circ$ and $19^\circ$ printed in Table 3 for $k = 3, 5, 6$ are too large: for $k = 3$, the boundary point $\bar h = \rho(e^{i\theta})/\sigma(e^{i\theta}) \approx -0.0761 + 1.0968i$ at $\theta \approx 53.78^\circ$ lies in the wedge $W_{88^\circ}$ but $\rho - \bar h \sigma$ has the root $e^{i\theta}$ on the unit circle. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
- E. Hairer and G. Wanner, *Solving Ordinary Differential Equations II: Stiff and Differential-Algebraic Problems*, 2nd edition, Springer, 1996, Chapter V (stability of the backward differentiation formulas), for the angles $86.03^\circ$, $73.35^\circ$, $51.84^\circ$ and $17.84^\circ$, which also follow from the boundary locus $\theta \mapsto \rho(e^{i\theta})/\sigma(e^{i\theta})$. <https://doi.org/10.1007/978-3-642-05221-7>
