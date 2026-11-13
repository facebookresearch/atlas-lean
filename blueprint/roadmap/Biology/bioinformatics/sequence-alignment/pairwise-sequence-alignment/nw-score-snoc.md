# The Needleman–Wunsch recurrence, end-peeling

Let
$\sigma : \alpha \to \alpha \to \mathbb{Z}$ be a substitution score and $g \in \mathbb{Z}$ a gap
score, and write $N(x, y)$ for the Needleman–Wunsch score of sequences $x, y$ over $\alpha$ with
respect to $\sigma$ and $g$. For all sequences $x, y$ and letters $a, b \in \alpha$, writing $xa$
for the sequence $x$ followed by the letter $a$,

$$N(xa, yb) = \max\bigl(N(x, y) + \sigma(a, b),\ N(x, yb) + g,\ N(xa, y) + g\bigr).$$
