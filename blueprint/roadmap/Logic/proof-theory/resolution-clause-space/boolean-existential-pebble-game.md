# The Boolean existential pebble game on a CNF formula

Let $\varphi$ be a CNF formula and $k \ge 1$. In the existential $k$-pebble game, Spoiler places pebbles on variables (at most $k$ at a time, removing pebbles at will) and Duplicator answers each newly pebbled variable with a truth value; Spoiler wins when the current partial assignment falsifies a clause of $\varphi$. A *winning strategy for Duplicator with $k$ pebbles* is a nonempty family $\mathcal{H}$ of partial assignments, each with domain of size at most $k$ and falsifying no clause of $\varphi$, closed under restriction, such that every member with domain of size less than $k$ extends within $\mathcal{H}$ to any further variable.

## Depends on

- [CNF formula](../../propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", Journal of Computer and System Sciences 74(3), 323–334, 2008: Definition 2.
