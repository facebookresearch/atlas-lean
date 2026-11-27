# Unbounded multipliers preserving almost-everywhere convergence to zero

Let $(f_n)_{n \in \mathbb{N}}$ be Borel measurable functions $\mathbb{R} \to \mathbb{R}$ with
$f_n(x) \to 0$ for almost every $x \in [0, 1]$. Then there are real numbers $c_n$ with
$|c_n| \to \infty$ such that still $c_n f_n(x) \to 0$ for almost every $x \in [0, 1]$.

## Idea

Almost-everywhere convergence to zero on a set of finite measure always leaves room for a slowly
growing factor. Since $\sup_{n \ge N} |f_n| \to 0$ almost everywhere on $[0, 1]$, one can choose
$N_1 < N_2 < \cdots$ so that the set where $\sup_{n \ge N_k} |f_n| > 2^{-k}$ has measure less than
$2^{-k}$, and put $c_n = k$ for $N_k \le n < N_{k+1}$. By the Borel–Cantelli lemma almost every
$x$ lies in only finitely many of these sets, so $|c_n f_n(x)| \le k 2^{-k}$ eventually.

## Statements

- [Unbounded multipliers preserving almost-everywhere convergence to zero](exists-tendsto-abs-at-top-and-ae-tendsto.md)
