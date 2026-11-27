# Sample compression for partial classes: logarithmic size suffices and is necessary

Every partial concept class $H$ of VC dimension $d$ has a sample compression scheme which compresses realizable samples of size $m$ to subsamples of size $\tilde O(d \log m)$. Conversely, there is a partial class of VC dimension $1$ such that every sample compression scheme for it has size $\Omega\big((\log m)^{1 - o(1)}\big)$ on samples of size $m$. In particular the sample compression conjecture fails for partial classes: no compression scheme of size bounded by a function of the VC dimension alone exists.

## Proof sketch

The upper bound uses the boosting construction of Moran and Yehudayoff with the one-inclusion-graph learner of the partial class as weak learner, which only needs the realizable PAC learnability of the class, giving size $O(d \log m)$ up to logarithmic factors. The lower bound converts a compression scheme of size $r$ on samples of size $m$ into a disambiguation of size $m^{O(r)}$ on $m$ points, so the disambiguation lower bound $m^{(\log m)^{1-o(1)}}$ forces $r \ge (\log m)^{1-o(1)}$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Generalization bound for sample compression schemes](../../../../generalization-bounds-and-concentration/generalization-bound-for-sample-compression-schemes.md)

## Proof depends on

- [Quasipolynomial Sauer–Shelah–Perles lemma for partial classes](partial-class-quasipolynomial-sauer-lemma.md)
- [A partial class of VC dimension one with no finite-VC disambiguation](vc-one-partial-class-without-disambiguation.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444.
