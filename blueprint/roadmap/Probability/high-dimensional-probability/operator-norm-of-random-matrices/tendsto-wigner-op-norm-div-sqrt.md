# Bai–Yin theorem

Under the hypotheses of the [strong Bai–Yin upper bound](wigner-op-norm-le-two-add.md)
(i.i.d. real entries $X_{ij}$, $i \le j$, with mean $0$, variance $1$ and finite fourth moment),
almost surely

$$\frac{\|M_n\|}{\sqrt{n}} \to 2 \quad (n \to \infty).$$

The upper bound is Bai and Yin's. The lower bound follows from the semicircle law: the semicircle
distribution gives positive mass to every neighbourhood of $\pm 2$, so a positive fraction of the
eigenvalues of $M_n / \sqrt{n}$ eventually lies beyond $2 - \varepsilon$ in absolute value.

## Informally uses

- [Strong Bai–Yin theorem, upper bound](wigner-op-norm-le-two-add.md): the upper half.
- [Wigner's semicircle law](../wigner-s-semicircle-law/wigner-semicircle.md): the lower half.

## Sources

- Z. D. Bai and Y. Q. Yin, "Necessary and sufficient conditions for almost sure convergence of the largest eigenvalue of a Wigner matrix", Ann. Probab. 16 (1988), no. 4, 1729–1741.
- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, Theorem 2.3.24 and the discussion after Theorem 2.4.2.
