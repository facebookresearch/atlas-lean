# k-wise independent hash families

Let $\iota$ be a finite nonempty set of seeds and $h : \iota \times X \to Y$ a family of functions into a finite set $Y$. The family is *$k$-wise independent* if for every set $T \subseteq X$ with $|T| \le k$, when the seed $i$ is uniform on $\iota$, the restriction $h_i|_T$ is uniformly distributed on $Y^T$; equivalently, the values at any $k$ distinct points are independent and uniform on $Y$. Wegman and Carter call such families strongly universal$_k$. For $k = 2$ this is pairwise independence, and for every $k \ge 2$ a $k$-wise independent family is pairwise independent. Consequently, for any functions $g_x : Y \to \mathbb{R}$, $x \in T$, $|T| \le k$, the average over seeds of $\prod_{x \in T} g_x(h_i(x))$ equals $\prod_{x \in T} \mathbb{E}_{y \in Y} g_x(y)$.

## Depends on

- [Pairwise-independent hashing by affine maps over GF(2)](../../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)
- [Uniform distribution on a finite type](../../../../Probability/distributions/discrete/discrete-uniform-distribution/uniform-fintype.md)

## Sources

- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences, 1981.
