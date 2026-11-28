# Natarajan's lemma

Let $\beta$ be a finite label set with $k = |\beta|$ and let $R \subseteq \beta^{n}$ be a set of labelings of $n$ points none of whose N-shattered sets (in the sense of Natarajan) has more than $d$ points. Then

$$
|R| \le \sum_{i=0}^{d} \binom{n}{i}\binom{k}{2}^{i}.
$$

If $k \ge 1$ the right side is at most $\big(\sum_{i \le d}\binom{n}{i}\big) k^{2d} \le (n+1)^d k^{2d}$; for $k = 2$ it is the Sauer-Shelah sum. The same bound holds for the labelings $(c(x_1), \dots, c(x_n))$ realized on sample points by any class $C$ of functions $X \to \beta$ that N-shatters no finite set of more than $d$ points.

## Proof sketch

Induct on $n$ by splitting off the first point. A labeling of the remaining points that extends with $s$ labels at the new point is counted once among the tails and at least $s - 1 \le \binom{s}{2}$ times among pairs of labels; for each unordered pair of labels, the tails extending with both labels of the pair N-shatter only sets of at most $d - 1$ points, since adding the new point to such a set would give an N-shattered set of size one larger. Pascal's rule for the sum closes the induction.

## Depends on

- [N-shattering](../natarajan-dimension-and-the-natarajan-lemma/nshatters.md)
- [Natarajan dimension at most d](../natarajan-dimension-and-the-natarajan-lemma/ndim-le.md)

## Sources

- B. K. Natarajan, "On Learning Sets and Functions", Machine Learning, 1989.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
