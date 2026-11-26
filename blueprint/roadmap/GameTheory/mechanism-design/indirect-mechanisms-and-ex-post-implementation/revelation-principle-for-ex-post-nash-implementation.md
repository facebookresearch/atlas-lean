# Revelation principle for ex-post Nash implementation

If an indirect quasilinear mechanism implements a social choice function $f$ in ex-post Nash equilibrium $s$, then the direct mechanism that, on reported types $t$, plays the indirect mechanism at $s(t)$ is truthful (truth-telling is an ex-post Nash equilibrium, and in fact DSIC on the induced valuation domains), implements the same $f$, and charges the same equilibrium payments. Every ex-post Nash equilibrium is also a Bayes–Nash equilibrium for every prior.

## Proof sketch

Compose the mechanism with $s$; a profitable misreport would translate into a profitable deviation within the range of $s$, contradicting the ex-post condition. Averaging the ex-post inequality over opponents' types gives the Bayes–Nash condition.

## Depends on

- [Game with incomplete information, dominant-strategy and ex-post Nash equilibria](game-with-incomplete-information-dominant-strategy-and-ex-post-nash-equilibria.md)
- [Revelation principle (dominant strategies)](../revelation-principle/revelation-principle-dominant-strategy.md)
- [Bayesian Nash equilibrium](../revelation-principle/is-bayes-nash.md)

## Proof depends on

- [Restricting action spaces turns ex-post Nash equilibria into dominant strategies](restricting-action-spaces-turns-ex-post-nash-equilibria-into-dominant-strategies.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
- Partha Dasgupta, Peter Hammond and Eric Maskin, "The Implementation of Social Choice Rules: Some General Results on Incentive Compatibility", The Review of Economic Studies, 1979.
