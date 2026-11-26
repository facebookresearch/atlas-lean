# Partial sums of totally multiplicative ±1 functions are often large

There is $\varphi : \mathbb{R} \to \mathbb{R}$, eventually nonnegative, with $\log\log\log\log\log X = o(\varphi(X))$ as $X \to \infty$, such that for every totally multiplicative sign function $f$ there is $c > 0$ with $\bigl|\sum_{n \le X} f(n)\bigr| \ge c\, \varphi(X)$ for arbitrarily large real $X$; here a totally multiplicative sign function is a function $f$ from the positive integers to $\{-1, 1\}$ with $f(mn) = f(m) f(n)$ for all positive integers $m, n$.

This resolves [AimPL question on lower bounds for partial sums of totally multiplicative ±1 functions](conjecture.md), the statement recorded as a proposition, in the affirmative; the resolution is in McNamara's PhD thesis, cited under Sources, as the remark on the problem list records, with growth $(\log\log X)^{1/484 - o(1)}$. The thesis bounds the discrepancy from below: for each $N$ the sum $\bigl|\sum_{i \le n} f(id)\bigr|$ is large for **some** $n \le N$ and some $d \le \exp(N)$. Complete multiplicativity, $f(id) = f(i) f(d)$, gives $\bigl|\sum_{i \le n} f(id)\bigr| = \bigl|f(d)\bigr| \bigl|\sum_{i \le n} f(i)\bigr| = \bigl|\sum_{i \le n} f(i)\bigr|$, independent of $d$, so the bound applies to the ordinary partial sum at that $n$. Multiplicativity on coprime arguments alone is not enough: the function that is $1$ on odd and $-1$ on even integers is multiplicative, and all its partial sums are at most $1$ in absolute value.

## Sources

- AimPL: Sarnak's conjecture, Section 1 (Lower bounds), item 1.4, http://aimpl.org/sarnakconjecture/1/.
- R. McNamara, PhD thesis, University of California, Los Angeles, https://escholarship.org/uc/item/4wr015m0.
