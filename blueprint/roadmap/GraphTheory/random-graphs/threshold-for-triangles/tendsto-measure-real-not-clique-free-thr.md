# Triangles are absent below the threshold 1/n

Let $p_n \in [0, 1]$ with $n p_n \to 0$. Then

$$\Pr[G(n, p_n) \text{ contains a triangle}] \to 0 .$$

Indeed the probability is at most $\binom n3 p_n^3 \le (n p_n)^3$.

## Informally uses

- [First moment bound for triangles in G(n, p)](measure-real-not-clique-free-three-le.md): the bound $\binom n3 p^3$.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Proposition 4.11 and its proof.
