# Atserias–Dalmau: the existential pebble game characterizes resolution width

Let $\varphi$ be a CNF formula and $w \ge 0$. If Duplicator has a winning strategy with $w + 1$ pebbles, then $\varphi$ has no resolution refutation of width at most $w$. Conversely, if $\varphi$ has no clause of width exactly $w + 1$ and no refutation of width at most $w$, then Duplicator wins with $w + 1$ pebbles. Thus for formulas of initial width at most $w$, the minimum refutation width is the least $w$ for which Spoiler wins the existential $(w+1)$-pebble game.

## Proof sketch

A winning family never falsifies a line of a width-$w$ proof: a position falsifying a resolvent restricts to its at most $w$ variables and extends to the resolved variable, falsifying a premise; but the empty clause is falsified by every position. Conversely, take as positions the partial assignments on at most $w+1$ variables falsifying no clause derivable in width $w$; extendability follows because two falsified extensions would yield a falsified derivable resolvent.

## Depends on

- [The Boolean existential pebble game on a CNF formula](boolean-existential-pebble-game.md)
- [Width of a derivation](../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Sources

- A. Atserias and V. Dalmau, "A Combinatorial Characterization of Resolution Width", Journal of Computer and System Sciences 74(3), 323–334, 2008: Lemmas 1–2 and Theorem 2 (stated there for $r$-CNF formulas).
