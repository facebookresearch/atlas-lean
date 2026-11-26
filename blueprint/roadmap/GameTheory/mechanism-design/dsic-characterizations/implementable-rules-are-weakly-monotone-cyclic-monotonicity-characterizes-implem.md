# Implementable rules are weakly monotone; cyclic monotonicity characterizes implementability

If a social choice rule $f$ is implementable in dominant strategies on domains $V$ (there exist payments making it DSIC), then $f$ is weakly monotone. Moreover $f$ is implementable on $V$ if and only if it is cyclically monotone on $V$.

## Proof sketch

Adding the incentive constraints for $v \to v'$ and $v' \to v$ cancels the payments and gives weak monotonicity. For cyclic monotonicity, the shortest-path potential on the graph of outcomes with edge lengths $v(a') - v(a)$ is well defined exactly when no negative cycle exists, and it furnishes the payments (Rochet's construction).

## Depends on

- [Weak monotonicity and cyclic monotonicity of social choice rules](weak-monotonicity-and-cyclic-monotonicity-of-social-choice-rules.md)
- [Dominant-strategy incentive compatibility](../revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Proof depends on

- [Taxation principle](taxation-principle.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ron Lavi, "Computationally Efficient Approximation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
