# Maker can force a win in the biased Maker-Breaker game

Fix a finite board $X$, a bias
$b \in \mathbb{N}$ and a property of finite sets, Maker's target. At a position $(M, R)$, where
$M$ and $R$ are the sets claimed so far by Maker and by Breaker, an element of $X$ is free if it
lies in neither $M$ nor $R$. The relation "Maker, to move at $(M, R)$, can force a win" is the
least one satisfying two rules: it holds when no element of $X$ is free and $M$ satisfies the
target; and it holds when there is a free element $e$ such that, for every set $R'$ of exactly
$\min(b, r)$ of the $r$ elements that are free after $e$ is claimed, Maker can force a win at
$(M \cup \{e\}, R \cup R')$. Thus Maker claims one free element per turn, Breaker answers with
$b$ of them (all remaining ones if fewer are free), play ends when the board is exhausted, and
Maker wins if his set satisfies the target.
