# Polygon gluings, matrix integrals and generating functions for Hultman numbers

**Definitions.** For $\pi \in S_n$ with $\pi_0 = 0$ and indices modulo $n + 1$, the **cycle graph** $G(\pi)$ is the directed graph on $\{0, 1, \dots, n\}$ with grey edges $i - 1 \to i$ and black edges $\pi_i \to \pi_{i-1}$. Each vertex has one incoming and one outgoing edge of each color, so the edges decompose uniquely into **alternating cycles**. The **Hultman number** $H(n,k)$ is the number of $\pi \in S_n$ whose cycle graph has exactly $k$ alternating cycles; $H(n,k) = 2\,S(n+2,k)/((n+1)(n+2))$ when $n - k$ is odd and $0$ otherwise, with $S$ the unsigned Stirling numbers of the first kind.

**Theorem.**

1. *(Polygon gluings.)* Take a $2n$-gon whose boundary consists of $n$ consecutive black sides followed by $n$ grey sides, the black sides oriented counterclockwise and the grey sides clockwise, and glue the black sides to the grey sides, respecting orientation, according to $\pi$. The result is a closed orientable surface of genus $g$ whose boundary graph has $k$ vertices with $2 - 2g = k - n + 1$, and the vertices correspond bijectively to alternating cycles of $G(\pi)$. Hence $H(n, n + 1 - 2g) = h_g(n)$, the number of genus-$g$ gluings.
2. *(Matrix integral.)* With $\mu_N$ the complex Ginibre measure $\propto e^{-\operatorname{Tr}(XX^*)}$ on $N \times N$ complex matrices,

$$p_n(N) := \sum_{g=0}^{\lfloor n/2\rfloor} H(n, n + 1 - 2g)\, N^{n - 2g + 1} = \int \operatorname{Tr}\big(X^n X^{*n}\big)\, d\mu_N(X).$$

3. *(Generating functions and recursions.)* With $F(x,N) = \sum_{g}\sum_{n \ge 2g} H(n, n+1-2g)\, N^{n-2g+1}\, x^n/n!$,

$$F(x,N) = \frac{1}{x^2}\Big(\frac{1}{(1 - x)^N} - (1 + x)^N\Big);$$

the genus counts satisfy $(n + 2)h_g(n) = (2n + 1)h_g(n-1) - (n-1)h_g(n-2) + n^2(n-1)h_{g-1}(n-2)$; the polynomials satisfy $(n + 2)p_n(N) = (2n + 1)N p_{n-1}(N) + (n - 1)(n^2 - N^2)p_{n-2}(N)$ with $p_0 = N$, $p_1 = N^2$; and the fixed-genus series $H_g(x) = \sum_n H(n, n+1-2g)x^n$ are rational: $H_0(x) = 1/(1-x)$ and, for $g \ge 1$, $H_g(x) = P_g(x)/(1 - x)^{1 + 4g}$ with $P_g$ an integer polynomial supported on degrees $2g, \dots, 4g - 2$, leading and trailing coefficients $a_{g,2g} = (2g)!/(g+1)$, $a_{g,4g-2} = 1$, and $P_g(1) = (4g - 1)!!/(2g + 1)$.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Expansion

Reading the two boundary cycles (grey $0 \to 1 \to \dots \to n$, black following $\pi$) as the two colored halves of a polygon identifies the cycle graph with the boundary graph of the gluing; Euler's formula then converts the cycle count into a genus. Wick's theorem for the complex Gaussian measure expands $\mathbb{E}\operatorname{Tr}(X^nX^{*n})$ as a sum over pairings of the $n$ factors $X$ with the $n$ factors $X^*$, i.e. over permutations, each weighted by $N^{\#\text{faces}}$; by the gluing bijection the number of faces is the number of alternating cycles, giving $p_n(N)$. The closed form of $F$ follows from the Stirling-number expression, since $\sum_k S(m,k)N^k = N(N+1)\cdots(N+m-1)$ is the coefficient extraction of $(1-x)^{-N}$, and the recursions are read off from linear differential equations satisfied by $F$. Small genus dominates: $H_0(x) = 1/(1-x)$ reflects that exactly one permutation of each size attains the maximal number $n + 1$ of cycles (the identity).

## Sources

- Nikita Alexeev, Peter Zograf, "Random Matrix Approach to the Distribution of Genomic Distance", Journal of Computational Biology 21 (2014), 622–631, <https://doi.org/10.1089/cmb.2013.0066>. Published version of arXiv:1111.3061, cited next; locators there refer to the arXiv version.
- Nikita Alexeev, Peter Zograf, "Hultman numbers, polygon gluings and matrix integrals", arXiv (2011). Theorems 1–3, Remarks 1–3. <https://doi.org/10.48550/arXiv.1111.3061>
