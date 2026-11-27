# Shuffle product identity (Ree)

Let every component $v^i$ of the velocity of $X$ be continuous. Then for all reals $s, t$ and
all words $I, J$,

$$S(X)^{I}_{s,t}\; S(X)^{J}_{s,t} = \sum_{K \in I ⧢ J} S(X)^{K}_{s,t},$$

the sum running over the [shuffles](shuffle.md) of $I$ and $J$ with multiplicity. For example
$S^1 S^2 = S^{12} + S^{21}$ and $S^{12} S^1 = 2 S^{112} + S^{121}$.

So the product of two linear functionals of the signature is again a linear functional of it: the
coordinate iterated integrals span an algebra of functions on paths, which contains the
constants ($S^\varnothing = 1$). This is the analogue for paths of the fact that products of
monomials are monomials, and the reason linear functionals of the signature can approximate
continuous functions of paths.

The proof here is by induction on $|I| + |J|$: both sides vanish at $t = s$ for nonempty words,
and by the product rule they have the same derivative in $t$, through the last-letter recursion
of the shuffle product. The source instead uses Fubini's theorem on the square
$[a,b]^2$; the decomposition of $I ⧢ J$ is the same.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Theorem 1.14, equation (13), and Example 1.15.
- T. Lyons, *Rough paths, signatures and the modelling of functions on streams*, Proc. ICM 2014,
  arXiv:1405.4537, Lemma 9.3 (attributed there to Ree).
