# Quadratic diversity from pairwise dissimilarities

Let $\iota$ be a finite index set, $Q$ a real $\iota \times \iota$ matrix and $w \in \mathbb{R}^\iota$ with $\sum_i w_i = 1$, and write $H_Q(w) = \sum_i w_i Q_{ii} - w^\top Q w$ (Rao's quadratic entropy form). Then:

- if $Q_{ij} = v_i + v_j - \delta_{ij}/2$ for all $i, j$, for some matrix $\delta$ and vector $v$, then $H_Q(w) = \frac12 w^\top \delta w - \frac12 \sum_i w_i \delta_{ii}$;
- for the canonical dissimilarity $\delta^Q_{ij} = Q_{ii} + Q_{jj} - 2Q_{ij}$, which has zero diagonal, $H_Q(w) = \frac12 w^\top \delta^Q w$.

A zero diagonal of $\delta$ is a sufficient condition for the short form $\frac12 w^\top \delta w$; for a given $w$ the exact condition is that the weighted diagonal correction $\sum_i w_i \delta_{ii}$ vanish. These are algebraic identities: neither $Q$ nor $\delta$ need be symmetric, and the weights may be negative, which extends the usual setting of a symmetric $Q$ and weights in the simplex. They carry no positivity, metric or concavity claim; those interpretations need further hypotheses, such as nonnegative weights.
