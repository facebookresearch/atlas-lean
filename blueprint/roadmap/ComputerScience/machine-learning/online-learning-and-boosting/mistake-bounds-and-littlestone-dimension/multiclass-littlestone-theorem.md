# Littlestone's theorem for arbitrary label sets: optimal mistake bound equals the multiclass Littlestone dimension

Let $C$ be a class of functions $X \to Y$ with $Y$ nonempty (any cardinality). A complete mistake tree of depth $d$ for $C$ has, at each internal node, an instance $x$ and two distinct labels $y_0 \ne y_1$, and every one of its $2^d$ root-to-leaf paths is realized by some $c \in C$. The (multiclass) Littlestone dimension $\mathrm{Ldim}(C) \in \mathbb{N} \cup \{\infty\}$ is the supremum of the depths of complete mistake trees (with $\mathrm{Ldim}(\emptyset) = 0$ here). In the realizable mistake-bound model with deterministic learners, the optimal worst-case number of mistakes $\mathrm{opt}(C)$ satisfies

$$
\mathrm{opt}(C) = \mathrm{Ldim}(C),
$$

both possibly infinite, and the standard optimal algorithm (predict a label whose version-space restriction is nonempty and has maximal Littlestone dimension) attains it. Because the learner is deterministic, adaptive adversaries are no stronger than fixed sequences.

## Proof sketch

An adversary walking down a complete $d$-tree can always choose the branch label differing from the prediction, forcing $d$ mistakes. Conversely, after a mistake of the standard optimal algorithm on a consistent example, the Littlestone dimension of the version space drops by at least one: otherwise trees for the true branch and the predicted branch would combine into a deeper tree. If no maximizing branch exists, the nonempty branches form an increasing chain of dimensions and the dimension is infinite.

## Depends on

- [The Littlestone dimension is the optimal mistake bound](../the-littlestone-dimension-is-the-optimal-mistake-bound.md)
- [Online classification protocol, mistakes and regret](../online-classification-protocol-mistakes-and-regret.md)

## Proof depends on

- [The Littlestone dimension is the optimal mistake bound](../the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Sources

- Nick Littlestone, "Learning Quickly When Irrelevant Attributes Abound: A New Linear-Threshold Algorithm", Machine Learning 2(4), 1988.
- Amit Daniely, Sivan Sabato, Shai Ben-David and Shai Shalev-Shwartz, "Multiclass Learnability and the ERM Principle", Journal of Machine Learning Research, 2015.
