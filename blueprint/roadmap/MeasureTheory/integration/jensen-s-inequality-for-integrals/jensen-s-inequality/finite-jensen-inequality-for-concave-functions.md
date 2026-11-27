# Finite Jensen inequality for concave functions

Let $s$ be a convex subset of a real vector space and $f : s \to \mathbb{R}$ a concave function. For finitely many points $p_1, \dots, p_n \in s$ and weights $w_i \ge 0$
with $\sum_i w_i = 1$,

$$\sum_{i=1}^n w_i f(p_i) \le f\Big(\sum_{i=1}^n w_i p_i\Big).$$

For instance, for a random variable $X$ with finitely many positive values, $E \log X \le \log E X$. The Mathlib declaration is more general: the
scalars may come from any linearly ordered field and the values may lie in an ordered module.

## Sources

- T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006: Theorem 2.6.2 (Jensen's inequality, stated for convex $f$; apply it to $-f$).
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842: `ConcaveOn.le_map_sum`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Convex/Jensen.lean#L72-L75.
