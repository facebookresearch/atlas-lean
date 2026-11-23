# The elimination learner

The elimination learner is a learner on labelled samples of truth assignments of $t$ variables, for $k \in \mathbb{N}$ and every sample size $m$: it runs the
elimination algorithm on the positive examples of the sample and outputs the Boolean function of
the resulting $k$-CNF expression. It reads only the labelled sample, never the target; the negative
examples are ignored.

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27 (1984), 1134-1142, Section 5, proof of Theorem A.
