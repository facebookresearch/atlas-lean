# Triangles appear above the threshold 1/n

Let $p_n \in [0, 1]$ with $n p_n \to \infty$. Then

$$\Pr[G(n, p_n) \text{ contains a triangle}] \to 1 .$$

For $n \ge 3$ one has $\binom n3 \ge n^3/162$, so the [second moment bound](measure-real-clique-free-three-le.md) gives $\Pr[\text{triangle-free}] \le 162/(np_n)^3 + 486/(np_n) \to 0$. Together with [the first half](tendsto-measure-real-not-clique-free-thr.md), $1/n$ is a threshold function for containing a triangle in the sense of Zhao's Definition 4.10.

## Informally uses

- [Second moment bound for triangles in G(n, p)](measure-real-clique-free-three-le.md): the bound on the probability of being triangle-free.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Definition 4.10, Proposition 4.11 and its proof.
