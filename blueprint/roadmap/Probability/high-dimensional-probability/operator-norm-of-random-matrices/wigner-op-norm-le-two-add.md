# Strong Bai–Yin theorem, upper bound

Let $(X_{ij})_{i \le j}$ be independent, identically distributed real random variables with
mean $0$, variance $1$ and finite fourth moment, and let $M_n$ be the $n \times n$ real symmetric
matrix with entries $X_{\min(i,j)\,\max(i,j)}$, so that the $M_n$ are the top-left blocks of one
infinite array. Then almost surely, for every $\varepsilon > 0$,
$\|M_n\| \le (2 + \varepsilon)\sqrt{n}$ for all sufficiently large $n$; that is,
$\limsup_{n \to \infty} \|M_n\| / \sqrt{n} \le 2$ almost surely.

The $\varepsilon$-form says the same as $\limsup \le 2$ without requiring the limit superior to be finite.

## Background

- [Upper tail estimate for Wigner ensembles](wigner-op-norm-upper-tail.md): background; for
  bounded entries the $\varepsilon$-net argument already gives $\|M_n\| = O(\sqrt{n})$, and the
  moment method with high powers $\operatorname{tr} M_n^{k}$, $k$ growing with $n$, sharpens the
  constant to $2$.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, Theorem 2.3.24.
- Z. D. Bai and Y. Q. Yin, "Necessary and sufficient conditions for almost sure convergence of the largest eigenvalue of a Wigner matrix", Ann. Probab. 16 (1988), no. 4, 1729–1741.
