# The number of periodic orbits of planar polynomial vector fields is not computable

No algorithm computes, from a planar polynomial vector field, the number of periodic orbits of the differential equation it defines, already on the unit ball and also on the whole plane over a uniformly separated family of polynomials.

For $p\colon \mathbb{R}^2 \to \mathbb{R}^2$ with polynomial components consider the planar system

$$
x' = p(x) .
$$

Let $\Theta$ be the operator that maps $p$ to the number of periodic orbits of this system in a domain $A \subseteq \mathbb{R}^2$. Computability is in the sense of computable analysis: $p$ is given by a name, a sequence of rational approximations of its coefficients with prescribed precision, and $\Theta$ is computable if an oracle Turing machine outputs $\Theta(p)$ from any name of $p$.

**Theorem.** The operator $\Theta$, which maps a function $p\colon A \subseteq \mathbb{R}^2 \to \mathbb{R}^2$ with polynomial components to the number of periodic orbits of $x' = p(x)$, is not computable when (Theorem A of the source):

1. $A$ is the unit ball;
2. $A = \mathbb{R}^2$. In this case there exist a family of polynomials $\{p_n\}_{n \in \mathbb{N}}$ and $\delta > 0$ with $\|p_n - p_m\| \ge \delta$ for $n \ne m$ such that $\Theta$ is not computable even on the set $\{p_n : n \in \mathbb{N}\}$.

The second item shows that the non-computability is not a consequence of discontinuity of $\Theta$. Moreover, this family $\{p_n\}$ has no computable sharp upper bound on the number of its periodic orbits (Theorem C). By contrast, the number of periodic orbits is uniformly computable, with their positions to arbitrary precision, on the set of $C^1$ structurally stable vector fields on the closed unit disk (Theorem B).

## Depends on

None.

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Let $g(k, i) = 1$ if the $k$-th Turing machine halts within $i$ steps on input $k$ and $g(k,i) = 0$ otherwise, and $G(k) = \sum_{i \ge 1} g(k,i)/2^{i+1}$; $G\colon \mathbb{N} \to [0, 1/2]$ is computable as a real-valued function, with $G(k) > 0$ exactly when the $k$-th machine halts on $k$. The cubic system

$$
x_1' = -x_2 + x_1(x_1^2 + x_2^2 - G(k)), \qquad x_2' = x_1 + x_2(x_1^2 + x_2^2 - G(k))
$$

reads $r' = r(r^2 - G(k))$, $\theta' = 1$ in polar coordinates, so it has one periodic orbit, the circle of radius $\sqrt{G(k)} < 1$, if the machine halts and none otherwise. Since $k \mapsto p_k$ is computable, a computable $\Theta$ would decide the diagonal halting problem $\{k : \text{the } k\text{-th machine halts on } k\}$ (Lemma 16 of the source), which is impossible; the same argument works on $\mathbb{R}^2$, and a further construction separates the polynomials uniformly.

## Sources

- D. S. Graça and N. Zhong, "Computing the exact number of periodic orbits for planar flows", Transactions of the American Mathematical Society 375 (2022), no. 8, 5491–5538, https://doi.org/10.1090/tran/8644; read in arXiv:2101.07701v2 (Theorems A, B and C in the introduction, Section 2 on computable analysis, and Lemma 16 and the proof of Theorems A and C in Section 4 of arXiv:2101.07701v2).
