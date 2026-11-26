# Thresholds: VC dimension one but Littlestone dimension $\lfloor \log_2(N+1) \rfloor$, infinite on infinite orders

On a linear order $X$, the threshold concept $c_\theta(x) = \mathbf{1}[x < \theta]$ and the class $C_X = \{c_\theta : \theta \in X\}$ satisfy:

1. no two points are shattered, so $\mathrm{VCdim}(C_X) = 1$ when $X$ has at least two points;
2. for $X = \mathbb{N}$ and $C_N = \{c_\theta : \theta \le N\}$ with $N \ge 1$: $\mathrm{VCdim}(C_N) = 1$ and $\mathrm{Ldim}(C_N) = \lfloor\log_2(N+1)\rfloor$; hence $2^n$ thresholds have optimal mistake bound exactly $n$;
3. on every infinite linear order (for example $\mathbb{N}$, $\mathbb{Q}$, $\mathbb{R}$) $\mathrm{Ldim}(C_X) = \infty$, and on a dense order even the thresholds inside any nonempty open interval have infinite Littlestone dimension.

Since thresholds are PAC learnable, this separates PAC learnability from finite mistake bounds.

## Proof sketch

A threshold labelling the larger of two points $1$ labels the smaller one $1$ too, so pairs are not shattered. Binary search on the midpoint of $2^k$ ordered thresholds builds a complete mistake tree of depth $k$, giving the lower bound; the halving bound on $N+1$ concepts gives the matching upper bound $\lfloor\log_2(N+1)\rfloor$. Infinite orders contain $2^k$ ordered points for every $k$.

## Depends on

- [Littlestone's theorem for arbitrary label sets: optimal mistake bound equals the multiclass Littlestone dimension](multiclass-littlestone-theorem.md)

## Proof depends on

- [Littlestone's theorem for arbitrary label sets: optimal mistake bound equals the multiclass Littlestone dimension](multiclass-littlestone-theorem.md)
- [Halving mistake bound](../../../not-yet-classified/halving/halving-mistakes-bound.md)
- [The fundamental theorem of PAC learning](../../pac-learning/is-paclearnable-realizable-family-iff-ha.md)

## Sources

- Nick Littlestone, "Learning Quickly When Irrelevant Attributes Abound: A New Linear-Threshold Algorithm", Machine Learning 2(4), 1988.
- Shai Shalev-Shwartz and Shai Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
