# The even tail of a perfect cover

Let $s = (s_1, \dots, s_{m+n})$, $s_i = (x_i, y_i)$, be a
family in $(\mathbb{Z}_2)^m \oplus \mathbb{Z}_{2^n}$ that is a perfect $1$-cover: every element of
the group is the sum of the $s_i$ over exactly one set of indices. Let $k + 1 \le m + n$ and suppose
that $y_i$, read as an integer in $\{0, \dots, 2^n - 1\}$, is odd exactly when $i \le k + 1$. Let
$V$ be the $\mathbb{Z}_2$-span of $x_{k+2}, \dots, x_{m+n}$ in $(\mathbb{Z}_2)^m$. Then every
$(x, y)$ with $x \in V$ and $y$ even (again read in $\{0, \dots, 2^n - 1\}$) is the sum of the
$s_i$ over exactly one set of indices taken from $\{k+2, \dots, m+n\}$.

## Sources

- John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 24 (`jis-2025-25.7.8-lem-24`). The family's elements lie in `V ⊕ 2ℤ_{2^n}` by hypothesis and by definition of `V`; only the covering statement is stated.
