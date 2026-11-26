# Subset-weight and random-order formulas for the Shapley value agree

For every cost-sharing game on a finite set $A$ with $n = |A|$, the Shapley value $\phi_i = \sum_{S \subseteq A \setminus \{i\}} \frac{|S|!\,(n - 1 - |S|)!}{n!} \bigl(c(S \cup \{i\}) - c(S)\bigr)$ equals the average, over all $n!$ orderings of $A$, of agent $i$'s marginal cost $c(P_i \cup \{i\}) - c(P_i)$ with respect to its set $P_i$ of predecessors.

## Proof sketch

Exactly $|S|!(n-1-|S|)!$ orderings have predecessor set $S$ for agent $i$.

## Depends on

- [Shapley's formula](../shapley-value/shapley-formula.md)
- [Cooperative game with transferable utility](../shapley-value/coop-game.md)

## Sources

- Eva Tardos and Vijay V. Vazirani, "Basic Solution Concepts and Computational Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
