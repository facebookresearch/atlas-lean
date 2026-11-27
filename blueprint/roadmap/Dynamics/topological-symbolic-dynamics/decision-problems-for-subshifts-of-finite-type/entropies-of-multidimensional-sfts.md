# Entropies of multidimensional SFTs are exactly the right recursively enumerable reals, so some are not computable

For every dimension $d \ge 2$, the topological entropies of $\mathbb{Z}^d$ subshifts of finite type are exactly the nonnegative right recursively enumerable real numbers; consequently there are subshifts of finite type whose entropy cannot be computed.

Let $X \subseteq \Sigma^{\mathbb{Z}^d}$ be a [subshift of finite type](subshifts-of-finite-type-on-groups.md), and let $N_n(X)$ be the number of patterns on the cube $\{0, \ldots, n-1\}^d$ that occur in points of $X$. Its *topological entropy* is $h(X) = \lim_{n \to \infty} n^{-d} \log N_n(X)$. A real number $h$ is *computable* if an algorithm, given $n$, outputs a rational $r(n)$ with $|h - r(n)| < 1/n$, and *right recursively enumerable* (upper semi-computable) if an algorithm, given $n$, outputs rationals $r(n) \ge h$ with $r(n) \to h$; equivalently, $\{q \in \mathbb{Q} : q > h\}$ is a recursively enumerable set.

**Theorem (Hochman–Meyerovitch).** For $d \ge 2$ the class of entropies of $d$-dimensional subshifts of finite type is the class of nonnegative right recursively enumerable numbers (Theorem 1.1 of the source). Since there are right recursively enumerable numbers that are not computable, there are subshifts of finite type whose entropy cannot be computed effectively.

The same class of numbers arises for $d$-dimensional sofic shifts (Theorem 1.2), while the entropy of an irreducible SFT, one in which any two admissible patterns far enough apart extend to a common configuration, is computable (Theorem 1.3). In dimension one, entropies of SFTs are the nonnegative rational multiples of logarithms of Perron numbers (Lind), all computable.

## Depends on

- [Subshifts of finite type on a finitely generated group and the domino problem](subshifts-of-finite-type-on-groups.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

That every entropy is right recursively enumerable follows because the number of locally admissible patterns on cubes, which can be counted, gives upper approximations converging to the entropy (Theorem 3.1, also due to Friedland). For the converse, given a Turing machine that computes a decreasing sequence of rationals converging to $h$, the source builds an SFT that simulates the machine in a self-similar hierarchical structure and uses its output to control the density of "free" symbols, which carry entropy, so that the entropy equals $h$. The existence of right recursively enumerable non-computable reals rests on the halting problem: the number $\sum_k \varepsilon_k 2^{-k}$, with $\varepsilon_k = 0$ exactly when the $k$-th machine halts, is an example. The hierarchical simulation construction has no page.

## Sources

- M. Hochman and T. Meyerovitch, "A characterization of the entropies of multidimensional shifts of finite type", Annals of Mathematics (2) 171 (2010), no. 3, 2011–2038, https://doi.org/10.4007/annals.2010.171.2011; read in arXiv:math/0703206v1 (Theorems 1.1, 1.2 and 1.3 and the remark between them in Section 1, and Theorem 3.1, of arXiv:math/0703206v1).
