# The first reflexive stabilization adds one monomial to the $h^*$-formula

**The first reflexive stabilization adds one monomial to the $h^*$-formula.** Let
$q = (q_1, \dots, q_n)$ be a list of natural numbers whose reflexive stabilization number is
$1$, so that its first reflexive stabilization is $\operatorname{rs}(q) = (1, q_1, \dots, q_n)$.
For a list $p = (p_1, \dots, p_m)$ of natural numbers put $|p| = p_1 + \dots + p_m$, let
$\ell(p) = \lfloor (1 + |p|) / \operatorname{lcm}(p) \rfloor$ (taken to be $0$ when
$\operatorname{lcm}(p) = 0$), let
$w(p, b) = b - \sum_{i=1}^{m} \lfloor p_i b / (1 + |p|) \rfloor$ be its weight statistic, and let
$h_p(z) = \sum_{b=0}^{|p|} z^{w(p, b)} \in \mathbb{Z}[z]$ be its explicit $h^*$-formula. Suppose
that $\ell(\operatorname{rs}(q)) = 1$. Then $h_{\operatorname{rs}(q)}(z) = h_q(z) + z^{n+1}$.

## Sources

- Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60, Theorem 12.
