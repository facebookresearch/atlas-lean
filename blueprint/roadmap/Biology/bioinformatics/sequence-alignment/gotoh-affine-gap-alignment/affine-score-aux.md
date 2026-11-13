# Affine-gap score from a gap state

Fix an integer substitution score $\sigma$, an integer
gap-open cost $o$ and an integer gap-extend cost $e$. The affine-gap score of an alignment started
from a gap state $p$ is the sum of its column scores, computed left to right while carrying a gap
state that starts at $p$ and is updated after each column. The empty alignment scores $0$. A
column pairing an element $a$ of the first sequence with an element $b$ of the second scores
$\sigma(a, b)$ and sets the state to $\mathrm{none}$. A column pairing an element of the first
sequence with a gap has kind $\mathrm{gapX}$, and a column pairing a gap with an element of the
second sequence has kind $\mathrm{gapY}$; such a column scores $e$ if the carried state equals its
kind and $o$ otherwise, and sets the state to its kind. A column of two gaps scores $0$ and sets
the state to $\mathrm{none}$.

The column of two gaps cannot occur in a valid alignment; it is scored as a no-op.
