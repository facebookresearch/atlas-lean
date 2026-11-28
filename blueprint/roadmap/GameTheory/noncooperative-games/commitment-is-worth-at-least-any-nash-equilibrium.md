# Commitment is worth at least any Nash equilibrium

In a bimatrix game with leader payoff matrix $A$ and follower payoff matrix $B$, under leader-favourable tie-breaking, the optimal value of
committing to a mixed strategy is at least $x^{*\top} A y^*$ for every mixed Nash equilibrium $(x^*, y^*)$.

## Proof

By the best-response condition every pure strategy $j$ in the support of $y^*$ is a follower best response to $x^*$. If the leader commits to $x^*$, the
follower picks a best response $j$ maximizing the leader's payoff among best responses, so the leader gets
$\max_{j \in \mathrm{BR}(x^*)} (x^{*\top} A)_j \ge \sum_j y^*_j (x^{*\top} A)_j = x^{*\top} A y^*$, since $y^*$ is a convex combination of best responses. The optimal
commitment value is at least this.

## Depends on

- [Optimal mixed strategy to commit to (two-player normal form)](optimal-mixed-strategy-to-commit-to.md)
- [Mixed Nash equilibrium](nash-s-theorem/is-mixed-nash.md)

## Proof depends on

- [Best response condition](bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash-iff.md)

## Sources

- V. Conitzer and T. Sandholm, *Computing the optimal strategy to commit to*, ACM EC 2006, Section 1 (commitment can only help the leader under favourable tie-breaking). Background reference. <https://users.cs.duke.edu/~conitzer/commitEC06.pdf>
