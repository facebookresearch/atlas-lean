# Babai's nearest-plane approximation bound

If $b_1, \dots, b_n$ is $\frac34$-reduced and $y$ is a vector of their integer span that satisfies the nearest-plane condition for a target $t$ (for instance, the output of Babai's nearest-plane algorithm), then for every vector $v$ of the integer span,

$$
\|t - y\| \le (\sqrt{2})^{n}\, \|t - v\| .
$$

Hence LLL followed by the nearest-plane algorithm approximates the closest vector problem within a factor $2^{n/2}$ in polynomial time (Regev, lecture notes "CVP", Lemma 6).

## Proof sketch

Compare the Gram-Schmidt coordinates of $t - y$ and $t - v$ from the last index down: at the largest index where $y$ and $v$ differ, $t - v$ has a coordinate of absolute value at least $\frac12\|b_j^*\|$, and reducedness bounds the later Gram-Schmidt lengths by powers of $2$.

## Depends on

- [Babai's nearest-plane algorithm](babai-nearest-plane-algorithm.md)
- [The Lenstra–Lenstra–Lovász algorithm](../lattice-basis-reduction/the-lenstralenstralovasz-algorithm.md)

## Proof depends on

- [LLL-reduced bases approximate the shortest lattice vector](lll-reduced-short-vector.md)

## Sources

- L. Babai, "On Lovász' Lattice Reduction and the Nearest Lattice Point Problem", Combinatorica 6(1), 1986.
- O. Regev, "Lattices in Computer Science", lecture notes, Tel Aviv University, 2004.
