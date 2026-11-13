# Appending to the second sequence loses at most one gap

Let
$\sigma : \alpha \to \alpha \to \mathbb{Z}$ be a substitution score, $g \in \mathbb{Z}$ a gap
score, and write $N(x, y)$ for the Needleman–Wunsch score of sequences $x, y$ over $\alpha$ with
respect to $\sigma$ and $g$. For all sequences $x, y$ and every letter $b \in \alpha$, writing
$yb$ for $y$ with $b$ appended at the end, $N(x, y) + g \le N(x, yb)$.

An optimal alignment of $x$ and $y$ followed by the gap column pairing nothing with $b$ is an
alignment of $x$ and $yb$.
