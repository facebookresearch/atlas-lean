# Shapley value of a database fact

Let $\alpha$ be a numerical query over a schema, and $D = D_x \cup D_n$ a database split into exogenous and endogenous facts.
Consider the [cooperative game](../../../GameTheory/cooperative-games/shapley-value/coop-game.md) whose players are the endogenous
facts $D_n$ and whose worth function is $v(E) = \alpha(E \cup D_x) - \alpha(D_x)$ for $E \subseteq D_n$. The *Shapley value* of an
endogenous fact $f$ for $\alpha$, written $\mathrm{Shapley}(D, \alpha, f)$, is the value of player $f$ in this game given by
[Shapley's formula](../../../GameTheory/cooperative-games/shapley-value/shapley-formula.md). A Boolean query $q$ is read as the
numerical query with values $0$ and $1$. If $q$ is monotone, $D_x \not\models q$ and $D \models q$, the game is a
simple game (monotone, $\{0, 1\}$-valued, $v(\emptyset) = 0$, $v(D_n) = 1$), and the value is the Shapley–Shubik index of $f$;
for a non-monotone $q$ a marginal contribution can be $-1$, as for "$R$ is empty" with the single endogenous fact $R(a)$ and
no exogenous facts.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Cooperative game with transferable utility](../../../GameTheory/cooperative-games/shapley-value/coop-game.md)
- [Shapley's formula](../../../GameTheory/cooperative-games/shapley-value/shapley-formula.md)

## Sources

- E. Livshits, L. Bertossi, B. Kimelfeld and M. Sebag, "The Shapley value of tuples in query answering", *Logical Methods in Computer Science* 17(3) (2021) 22; conference version ICDT 2020; arXiv:1904.08679 <https://arxiv.org/abs/1904.08679>, Section 2 (formula (2.3)) and Definition 3.1.
