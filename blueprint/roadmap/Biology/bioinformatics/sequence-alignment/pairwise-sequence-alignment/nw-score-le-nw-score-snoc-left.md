# Appending to the first sequence loses at most one gap

Let
$\sigma : \alpha \to \alpha \to \mathbb{Z}$ be a substitution score, $g \in \mathbb{Z}$ a gap
score, and write $N(x, y)$ for the Needleman–Wunsch score of sequences $x, y$ over $\alpha$ with
respect to $\sigma$ and $g$. For all sequences $x, y$ and every letter $a \in \alpha$, writing
$xa$ for $x$ with $a$ appended at the end, $N(x, y) + g \le N(xa, y)$.

An optimal alignment of $x$ and $y$ followed by the gap column pairing $a$ with nothing is an
alignment of $xa$ and $y$.
