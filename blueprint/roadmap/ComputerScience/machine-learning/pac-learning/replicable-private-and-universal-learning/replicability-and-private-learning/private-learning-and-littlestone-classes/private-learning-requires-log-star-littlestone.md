# Private learning requires log-star of the Littlestone dimension samples

Every $(1/16, 1/16)$-accurate $(0.1, O(1/(n^2 \log n)))$-differentially private learner for a class $H$ of Littlestone dimension $d$, proper or improper, uses $n = \Omega(\log^* d)$ examples. In particular, the class of thresholds over $\mathbb{N}$ (VC dimension one, infinite Littlestone dimension) is not privately learnable, and every privately learnable class has finite Littlestone dimension.

## Proof sketch

By the threshold lemma it suffices to show that privately learning thresholds on an ordered domain of size $N$ needs $\Omega(\log^* N)$ samples. Given a private learner on $n$ examples, color each increasing $n$-tuple of domain points by the (discretized) behavior of the learner on the corresponding threshold samples; Ramsey's theorem for hypergraphs yields a large homogeneous set when $N$ exceeds a tower of height about $n$. On a homogeneous set the learner's outputs cannot locate the threshold, which together with privacy-based packing gives a contradiction, so $N$ must be at most a tower of height $O(n)$.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Large Littlestone dimension forces large threshold subclasses](littlestone-dimension-contains-thresholds.md)
- [Packing lower bound for pure differential privacy](../../../../../cryptography/differential-privacy/packing-lower-bound-for-pure-differential.md)

## Sources

- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949.
