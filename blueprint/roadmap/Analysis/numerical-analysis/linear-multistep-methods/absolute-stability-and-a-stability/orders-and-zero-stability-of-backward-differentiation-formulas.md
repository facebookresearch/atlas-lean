# Orders and zero-stability of the backward differentiation formulas

For $1 \le k \le 6$ the $k$-step [backward differentiation formula](backward-differentiation-formulas.md) has order $k$, is zero-stable, and is stiffly stable and A(α)-stable with the constants below; for $k \ge 7$ the backward differentiation formula of order $k$ is not zero-stable.

| $k$ | $C_{k+1}$ | $a$ in stiff stability | $\alpha$ in A(α)-stability |
|---|---|---|---|
| 1 | $-\tfrac12$ | $0$ | $90^\circ$ |
| 2 | $-\tfrac29$ | $0$ | $90^\circ$ |
| 3 | $-\tfrac3{22}$ | $0.1$ | $88^\circ$ |
| 4 | $-\tfrac{12}{125}$ | $0.7$ | $73^\circ$ |
| 5 | $-\tfrac{10}{137}$ | $2.4$ | $52^\circ$ |
| 6 | $-\tfrac{20}{343}$ | $6.1$ | $19^\circ$ |

The methods with $k = 1, 2$ are A-stable; the angles for $k \ge 3$ are rounded.

## Depends on

- [Backward differentiation formulas](backward-differentiation-formulas.md)
- [Zero-stability](../zero-stability.md)
- [Stiff stability](stiff-stability.md)
- [A(α)-stability](a-alpha-stability.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.2, Table 3 (coefficients, order, error constant and stability parameters for $k = 1, \dots, 6$) and the statement after it that for $p \ge 7$ these methods are not zero-stable. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
