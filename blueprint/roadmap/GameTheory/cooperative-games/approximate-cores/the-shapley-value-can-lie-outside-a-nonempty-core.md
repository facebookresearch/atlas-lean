# The Shapley value can lie outside a nonempty core

There is a three-agent metric facility location game whose core is nonempty (containing the cost shares $(4, 2, 2)$) but whose Shapley value $(23/6, 11/6, 7/3)$ violates the core constraint of a two-agent coalition, charging it $25/6$ while its stand-alone cost is $4$. There are also metric facility location games with empty core.

## Proof sketch

Compute all seven coalition costs of the explicit instance, average marginal costs over the six orderings, and compare with the coalition costs.

## Depends on

- [Cooperative facility location game](cooperative-facility-location-game.md)
- [Shapley's formula](../shapley-value/shapley-formula.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007, Examples 15.2, 15.4 and 15.24.
