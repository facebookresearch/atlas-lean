# Base vectors of a matroid are M-convex

For every matroid $M$ on $\iota$, the set of indicator vectors of its finite bases is
M-convex.

Write $\alpha = e_{B_1}$ and $\beta = e_{B_2}$. The condition $\alpha_i > \beta_i$ says
$i \in B_1 \setminus B_2$, and the base exchange axiom gives $j \in B_2 \setminus B_1$ with
$(B_1 \setminus \{i\}) \cup \{j\}$ a base; then $\alpha_j < \beta_j$ and
$\alpha - e_i + e_j$ is the indicator vector of that base.

This is the implication (8) ⇒ (7) of Brändén and Huh's Theorem 3.10.

## Sources

- P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Theorem 3.10, https://arxiv.org/abs/1902.03719.
