# Ben-Or's lower bound for algebraic computation trees

Let $W \subseteq \mathbb{R}^n$ and let $T$ be an algebraic computation tree of complexity $h$ that solves the membership problem for $W$. If $W$ has $N$ connected components then $2^h 3^{n + h} \ge N$. Applying this to $W$ and to its complement,

$$C(W) \ge \frac{\log_2 N - n \log_2 3}{1 + \log_2 3}, \qquad N = \max\{\#W, \#(\mathbb{R}^n \setminus W)\},$$

where $\#$ counts connected components; that is, $C(W) \ge a \log_2 N - b\,n$ with $a = 1/(1 + \log_2 3)$ and $b = \log_2 3/(1 + \log_2 3)$.

## Depends on

- [Algebraic computation tree](algebraic-computation-tree.md)

## Proof depends on

- [Connected components of a basic semialgebraic set](connected-components-of-a-basic-semialgebraic-set.md)

## Sources

- M. Ben-Or, "Lower bounds for algebraic computation trees", *Proceedings of the 15th Annual ACM Symposium on Theory of Computing*, 1983, pp. 80–86, <https://doi.org/10.1145/800061.808735>: Section 4, Theorem 3 ($2^h 3^{n+h} \ge N$) and Theorem 4 (the bound on $C(W)$ with $N = \max\{\#W, \#(\mathbb{R}^n - W)\}$)
