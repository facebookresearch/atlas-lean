# Entropy of a Bernoulli shift

Let $S$ be a finite alphabet with its discrete σ-algebra and $p$ a probability vector on $S$. The
Bernoulli scheme with probability vector $p$, the left shift on $S^{\mathbb{N}}$ with the product measure
$p^{\mathbb{N}}$, has Kolmogorov–Sinai entropy

$$h(\sigma) = -\sum_{s \in S} p(s) \log p(s).$$

Sarig states the formula with $\log = \log_2$; with the natural logarithm, as above, both sides change by the
same factor $1/\log 2$. The inequality [$h(\sigma) \ge H(p)$](of-real-le-ks-entropy-shift.md) already follows from
the time-zero partition alone.

## Informally uses

- [Sinai's generator theorem, noninvertible case](ks-entropy-eq-entropy-rel-of-is-strong-g.md): the source's
  proof notes that the partition into 1-cylinders is a strong generator, so the entropy is the entropy
  relative to that partition.
- [Entropy of the refined time-zero partition](partition-entropy-iterate-join-time-zero.md): the refinement
  into $n$-cylinders has entropy $n$ times $-\sum_s p(s) \log p(s)$, because the coordinates are independent.

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Proposition 4.6 and its proof.
