# Probabilistic serial is sd-efficient and sd-envy-free but not sd-strategy-proof

The probabilistic serial rule, in which all agents simultaneously eat their favourite remaining object at unit speed during the time interval $[0, 1]$, produces a bistochastic matrix that is sd-efficient (hence ex-post efficient), sd-envy-free and satisfies equal treatment of equals, but it is not sd-strategy-proof.

## Proof sketch

At every moment each agent eats its best available object, so it never prefers another agent's eaten share at any time, giving sd-envy-freeness; an object is exhausted before anyone starts eating a worse one only if nobody preferring it remains, so the trading relation is acyclic. A three-agent example exhibits a profitable misreport.

## Depends on

- [Random assignment and stochastic-dominance properties](random-assignment-and-stochastic-dominance-properties.md)

## Proof depends on

- [sd-efficiency is equivalent to acyclicity of the trading relation](sd-efficiency-is-equivalent-to-acyclicity-of-the-trading-relation.md)

## Sources

- Anna Bogomolnaia and Herve Moulin, "A New Solution to the Random Assignment Problem", Journal of Economic Theory, 2001.
