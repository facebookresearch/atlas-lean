# Average sensitivity of multilinear polynomial thresholds

Let $1\le d\le n$ and $n\ge1$. Let $p\in\mathbb R[X_1,\ldots,X_n]$ have total degree at most $d$ and each support monomial have exponent at most one in every variable. On $\{-1,1\}^n$ define $f(x)=1$ when $p(x)\ge0$, and $-1$ otherwise. If $x^{(i)}$ flips coordinate $i$, then $\sum_i 2^{-n}|\{x:f(x)\ne f(x^{(i)})\}|\le 8d\sqrt n$.

## Depends on

- Multilinear monomial support and uniform cube, coordinate flip, sign positive at zero, and average sensitivity.

## Proof outline

Relate edge counting and average sensitivity and give the degree-sensitive bound without assuming strict nonvanishing at cube vertices. Check zero and constant polynomials contribute zero. This does not identify extremizers.

- Dimension-and-degree uniform influence estimate for multilinear thresholds.

## Sources

- [Comparator statement: `OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GotsmanLinial.lean#L49-L51)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/127.md)
