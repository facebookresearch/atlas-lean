# Gross-substitutes valuations are submodular

Every gross-substitutes valuation $v$ satisfies $v(S \cup \{a, b\}) + v(S) \le v(S \cup \{a\}) + v(S \cup \{b\})$ for items $a, b \notin S$; equivalently marginal values decrease as the bundle grows, so $v$ is submodular.

## Proof sketch

Choose prices making $S$ free, the items outside $S \cup \{a,b\}$ prohibitive, and $a, b$ priced so that both are demanded; raising the price of $b$ slightly must keep $a$ demanded, which yields the inequality.

## Depends on

- [Gross-substitutes valuation](gross-substitutes-valuation.md)
- [Submodular set function](../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- Faruk Gul and Ennio Stacchetti, "Walrasian Equilibrium with Gross Substitutes", Journal of Economic Theory, 1999.
- Liad Blumrosen and Noam Nisan, "Combinatorial Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
