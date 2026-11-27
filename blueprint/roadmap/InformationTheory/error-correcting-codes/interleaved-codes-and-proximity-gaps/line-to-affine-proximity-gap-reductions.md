# Line-to-affine and affine-to-curve reductions for proximity gaps

Let $\mathbb{F}$ be a finite field, $P$ a property of words in $\mathbb{F}^n$, and $u_0, u_1, \dots, u_\ell \in \mathbb{F}^n$.

(1) If $P$ satisfies a line dichotomy with threshold $B$ (whenever more than $B$ points of a line $a + t b$ satisfy $P$, all of them do), then either every point $u_0 + \sum_j z_j u_j$ of the affine space satisfies $P$, or $(|\mathbb{F}| - 1)\cdot|\{z : P(u_0 + \sum_j z_j u_j)\}| \le B\,(|\mathbb{F}|^\ell - 1)$, a density at most $B/(|\mathbb{F}| - 1)$ independent of $\ell$.

(2) If correlated agreement holds for degree-$\ell$ curves above $B$ good scalars, then it holds for the affine space $u_0 + \sum_{j=1}^{\ell} z_j u_j$ ($\ell \ge 1$) whenever more than $(B + \ell)\,|\mathbb{F}|^{\ell - 1}$ points $z$ are good.

## Proof sketch

For (1), if some point $p$ fails $P$, every line through $p$ has at most $B$ good points; these lines partition the rest of the affine space into $(|\mathbb{F}|^\ell - 1)/(|\mathbb{F}| - 1)$ punctured lines. For (2), discard the at most $\ell|\mathbb{F}|^{\ell-1}$ tuples with a zero coordinate and write the others as $(a_j t^j)_j$ with $a \in (\mathbb{F}^\times)^\ell$, $t \in \mathbb{F}^\times$; averaging over $a$ finds a curve $t \mapsto u_0 + \sum_j t^j a_j u_j$ with more than $B$ good parameters, and unscaling its codewords by $a_j^{-1}$ gives the affine agreement.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
