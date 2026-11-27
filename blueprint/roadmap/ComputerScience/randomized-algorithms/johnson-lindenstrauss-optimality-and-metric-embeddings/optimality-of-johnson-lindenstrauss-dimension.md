# Larsen-Nelson optimality of the Johnson-Lindenstrauss dimension

1. (Arbitrary maps.) For all integers $n, d \ge 2$ and every $\varepsilon$ with $(\lg n)^{0.5001}/\sqrt{\min\{n, d\}} < \varepsilon < 1$ there is a set $X \subset \mathbb{R}^d$ of $n$ points such that every map $f : X \to \mathbb{R}^m$ with $(1 - \varepsilon)\|x - y\|_2^2 \le \|f(x) - f(y)\|_2^2 \le (1 + \varepsilon)\|x - y\|_2^2$ for all $x, y \in X$ has

$$
m = \Omega\bigl(\varepsilon^{-2}\lg(\varepsilon^2 n)\bigr).
$$

   The hypothesis gives $\varepsilon^{-2}\lg(\varepsilon^2 n) < d$, so the bound never exceeds the ambient dimension. If moreover $\varepsilon^2 n \ge n^{\gamma}$ for a fixed $\gamma > 0$, then $\lg(\varepsilon^2 n) \ge \gamma \lg n$ and the bound becomes $m = \Omega(\varepsilon^{-2}\log n)$.

2. (Linear maps.) There is a constant $C$ such that for all $n > 1$, $0 < \varepsilon < 1/2$ and $N > n^{C}$ there is an $N$-point set $X \subset \mathbb{R}^n$ such that every linear map $\mathbb{R}^n \to \mathbb{R}^m$ with distortion at most $1 + \varepsilon$ on $X$ has $m = \Omega(\min\{n, \varepsilon^{-2}\log N\})$.

With the Johnson-Lindenstrauss upper bound $O(\varepsilon^{-2}\log n)$, part 1 gives $m(n, d, \varepsilon) = \Theta(\varepsilon^{-2}\log n)$ whenever $\varepsilon$ satisfies its hypothesis and $\varepsilon^2 n \ge n^{\gamma}$ for a fixed $\gamma > 0$, improving Alon's bound by the factor $\log(1/\varepsilon)$.

## Proof sketch

Part 1 is an encoding argument: consider a large family of point sets, each consisting of $0$, the standard basis vectors and many sparse vectors built from them. If every set in the family embedded into dimension $m = o(\varepsilon^{-2}\lg(\varepsilon^2 n))$, one could round the embedded points to a fine net and recover from the rounded embedding which sparse vectors are present, since inner products are preserved up to $O(\varepsilon)$; this encodes each set of the family with fewer bits than the logarithm of the family size, a contradiction. Part 2 runs a related net-and-counting argument against the much smaller family of linear maps.

## Depends on

- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)

## Proof depends on

- [Rank lower bound for perturbed identity matrices](rank-of-perturbed-identity-matrices.md)
- [Johnson–Lindenstrauss lemma](../../../Geometry/metric-geometry/johnson-lindenstrauss.md)

## Sources

- Kasper Green Larsen, Jelani Nelson, "Optimality of the Johnson-Lindenstrauss Lemma", FOCS (2017), arXiv:1609.02094.
- Kasper Green Larsen, Jelani Nelson, "The Johnson-Lindenstrauss Lemma Is Optimal for Linear Dimensionality Reduction", ICALP (2016).
