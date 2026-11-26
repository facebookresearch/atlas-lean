# Balanced off-diagonal coloring of a $g \times g$ matrix with $K$ colours

Let $K \ge 2$ and $g$ be natural numbers with $3K^8 \le g$, and let $c = (c_{ab})_{0 \le a, b < g}$
be a symmetric matrix of natural numbers whose off-diagonal row sums satisfy
$\sum_{b \ne a} c_{ab} \le P$ for every $a$. Then there is a colouring
$\chi : \{0, \dots, g - 1\} \to \{0, \dots, K - 1\}$ whose colour classes all satisfy
$K \cdot |\chi^{-1}(\gamma)| < 2g$ and such that

$$
K^3 \sum_{a \in \chi^{-1}(\gamma)} \sum_{b \in \chi^{-1}(\gamma')} c_{ab} \le K \sum_{a} \sum_{b \ne a} c_{ab} + gP
$$

for all distinct colours $\gamma \ne \gamma'$. This is the
[off-diagonal balanced coloring theorem](exists-balanced-coloring-off-diagonal.md) for the index
set $\{0, \dots, g - 1\}$ and the colour set $\{0, \dots, K - 1\}$.
