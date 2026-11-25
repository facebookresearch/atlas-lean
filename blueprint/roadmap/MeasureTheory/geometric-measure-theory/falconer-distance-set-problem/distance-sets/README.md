# Distance set

For a set $E \subseteq \mathbb{R}^d$, the distance set of $E$ is
$\Delta(E) = \{|x - y| : x, y \in E\}$, the set of Euclidean distances between pairs of points of
$E$.

## Idea

Falconer's distance set problem asks how large a set must be for its distance set to be large: how
much Hausdorff dimension of $E$ forces $\Delta(E)$ to have positive length. It is a continuous
analogue of Erdős's question on the number of distinct distances determined by $n$ points. The
basic facts here make the question well posed: for compact $E$ the distance set is compact, hence
Borel, so its Lebesgue measure is defined, and it lies in $[0, \infty)$.

## Statements

- [Euclidean distance set](distance-set.md)
- [Distance set of the empty set](distance-set-empty.md): a basic fact: the empty set has empty distance set.
- [Distance set of a singleton](distance-set-singleton.md): a basic fact: a single point has distance set $\{0\}$.
- [Distances are nonnegative](distance-set-subset-nonnegative.md): a basic fact: distance sets lie in $[0, \infty)$.
- [Distance sets of compact sets are compact](distance-set-is-compact.md): a basic fact for compact sets.
- [Distance sets of compact sets are Borel](distance-set-measurable-set.md): a consequence of compactness: the length of the distance set is defined.
