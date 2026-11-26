# Balanced coloring with bounded off-diagonal block weight

Let $I$ and $\Gamma$ be finite sets with $g = |I|$ and $K = |\Gamma| \ge 2$ elements, and suppose
that $3K^8 \le g$. Let $c = (c_{ab})_{a, b \in I}$ be a symmetric matrix of natural numbers whose
off-diagonal row sums satisfy $\sum_{b \ne a} c_{ab} \le P$ for every $a \in I$; the diagonal
entries are arbitrary. Then there is a colouring $\chi : I \to \Gamma$ whose colour classes all
satisfy $K \cdot |\chi^{-1}(\gamma)| < 2g$ and such that

$$
K^3 \sum_{a \in \chi^{-1}(\gamma)} \sum_{b \in \chi^{-1}(\gamma')} c_{ab} \le K \sum_{a \in I} \sum_{b \ne a} c_{ab} + gP
$$

for all distinct colours $\gamma \ne \gamma'$. No diagonal entry occurs on the left, since distinct
colour classes are disjoint.
