# Sample compression for partial classes: logarithmic size suffices and is necessary

Every partial concept class $H$ of VC dimension $d$ has a sample compression scheme which compresses realizable samples of size $m$ to subsamples of size $\tilde O(d \log m)$. Conversely, there is a partial class of VC dimension $1$ such that every sample compression scheme for it has size $\Omega\big((\log m)^{1 - o(1)}\big)$ on samples of size $m$. In particular the sample compression conjecture fails for partial classes: no compression scheme of size bounded by a function of the VC dimension alone exists.

## Proof sketch

The upper bound uses the boosting construction of Moran and Yehudayoff with the one-inclusion-graph learner of the partial class as weak learner, which only needs the realizable PAC learnability of the class, giving size $O(d \log m)$ up to logarithmic factors. For the lower bound, a compression scheme of size $k$ for a class on a finite domain of $m$ points yields a disambiguation of size at most $(cm/k)^k$ for a numerical constant $c$, so the disambiguation lower bound $m^{(\log m)^{1-o(1)}}$ forces $k \ge (\log m)^{1-o(1)}$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Labelled sample compression scheme](../../../sample-compression-schemes/labelled-sample-compression-scheme.md)

## Proof depends on

- [VC dimension characterizes PAC learnability of partial concept classes](partial-class-pac-characterization.md)
- [A partial class of VC dimension one with no finite-VC disambiguation](vc-one-partial-class-without-disambiguation.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Theorem 7 and Proposition 14.
