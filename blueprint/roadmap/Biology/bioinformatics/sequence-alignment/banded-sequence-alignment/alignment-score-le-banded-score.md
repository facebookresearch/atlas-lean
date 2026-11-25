# Every banded alignment scores at most the banded score

Let $\sigma$ be integer substitution scores, $g$ an integer gap score and $w$ a band width. If $A$ is a [valid alignment](../pairwise-sequence-alignment/is-alignment.md) of sequences $x$ and $y$ that is [$w$-banded](is-banded.md), and the [banded score](banded-score.md) of $x$ and $y$ is defined and equals $s$, then the [alignment score](../pairwise-sequence-alignment/alignment-score.md) of $A$ with respect to $\sigma$ and $g$ is at most $s$.
