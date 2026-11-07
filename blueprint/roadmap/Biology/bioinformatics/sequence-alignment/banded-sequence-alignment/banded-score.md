# Banded alignment score

Fix a substitution score $\sigma$, assigning an integer
$\sigma(a, b)$ to each pair of letters $a$, $b$, an integer gap score $g$ and a band width
$w \in \mathbb{N}$. The banded alignment score of two sequences $x$ and $y$ is the maximum, over
all valid alignments of $x$ and $y$ that are banded with width $w$, of the (integer) alignment
score with respect to $\sigma$ and $g$. It has no value (it is the empty optional value) when no
such alignment exists.
