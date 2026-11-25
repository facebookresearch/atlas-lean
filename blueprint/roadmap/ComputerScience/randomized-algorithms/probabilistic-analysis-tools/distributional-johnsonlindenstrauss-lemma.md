# Distributional Johnson–Lindenstrauss lemma

Let $1 \le k < d$ and $0 < \varepsilon < 1$. Let $f : \mathbb{R}^d \to \mathbb{R}^k$ be the random linear map that orthogonally projects onto a uniformly random $k$-dimensional subspace, expresses the result in an orthonormal basis of that subspace, and scales by $\sqrt{d/k}$.

**Theorem.** For every fixed vector $v \in \mathbb{R}^d$:
1. $\Pr\bigl[\|f(v)\|^2 \le (1 - \varepsilon)\|v\|^2\bigr] \le \exp(-k\varepsilon^2/4)$;
2. $\Pr\bigl[\|f(v)\|^2 \ge (1 + \varepsilon)\|v\|^2\bigr] \le \exp\bigl(-\tfrac{k}{2}(\varepsilon^2/2 - \varepsilon^3/3)\bigr)$.

Hence $\|f(v)\|^2$ lies within a factor $1 \pm \varepsilon$ of $\|v\|^2$, except with probability at most $2\exp\bigl(-\tfrac{k}{2}(\varepsilon^2/2 - \varepsilon^3/3)\bigr)$. This failure probability decays exponentially in $\varepsilon^2 k$.

**Proof.** By rotation invariance, assume $\|v\| = 1$. Then the distribution of $\|f(v)\|^2 \cdot k/d$ equals that of $L = Y_1^2 + \cdots + Y_k^2$ for a uniformly random unit vector $Y \in S^{d-1}$, whose mean is $\mu = k/d$. Represent $Y = X/\|X\|$ with $X$ a standard Gaussian vector. Then the moment-generating-function method gives
$\Pr[L \le \beta k/d] \le \exp\bigl(\tfrac{k}{2}(1 - \beta + \ln\beta)\bigr)$ for $\beta < 1$, and the same bound for $\Pr[L \ge \beta k/d]$ when $\beta > 1$. Taking $\beta = 1 \mp \varepsilon$ and using $\ln(1 - x) \le -x - x^2/2$ and $\ln(1 + x) \le x - x^2/2 + x^3/3$ gives the two bounds.

**Corollary.** Apply the theorem to the $\binom{N}{2}$ difference vectors of an $N$-point set and take a union bound. If $k \ge 4(\varepsilon^2/2 - \varepsilon^3/3)^{-1}\ln N$, then $f$ preserves all pairwise squared distances within $1 \pm \varepsilon$ with positive probability, indeed with probability at least $1/N$. This is the [Johnson–Lindenstrauss lemma](../../../Geometry/metric-geometry/johnson-lindenstrauss.md).

## Background

- [Johnson–Lindenstrauss lemma](../../../Geometry/metric-geometry/johnson-lindenstrauss.md)

## Sources

- S. Dasgupta and A. Gupta, "An elementary proof of a theorem of Johnson and Lindenstrauss", *Random Structures & Algorithms* 22(1):60–65, 2003, <https://cseweb.ucsd.edu/~dasgupta/papers/jl.pdf>: Lemma 2.2(a) and (b), the tail bounds for the squared length of the projection of a random unit vector onto $k$ coordinates, proved with Gaussian moment generating functions; and Theorem 2.1 with its proof, which derives the bounds $\exp(-k\varepsilon^2/4)$ and $\exp(-\tfrac{k}{2}(\varepsilon^2/2 - \varepsilon^3/3))$, the union bound, and the threshold $k \ge 4(\varepsilon^2/2 - \varepsilon^3/3)^{-1}\ln n$.
