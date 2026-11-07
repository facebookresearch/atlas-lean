# Sobolev embedding theorem (Morrey regime)

Let $n, k, r$ be natural numbers and
$\alpha, p$ real numbers with $n < p$, $0 < \alpha \le 1$ and $r + \alpha < k - n/p$. Then every
function $f : \mathbb{R}^n \to \mathbb{R}$ in the Sobolev space $W^{k,p}(\mathbb{R}^n)$ is equal
almost everywhere, for Lebesgue measure, to some function $g$ in the Hölder space
$C^{r,\alpha}(\mathbb{R}^n)$.

## Sources

- C.B. Morrey, 'Functions of several variables and absolute continuity, II', Duke Math. J. 6 (1940) 187–215; full Sobolev-embedding development in *Multiple Integrals in the Calculus of Variations*, Springer 1966. Listed as §111 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `sobolev_embedding_morrey`.
