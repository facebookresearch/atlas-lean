# Open Gale–Stewart games are determined

In every Gale–Stewart game that is open for one of the players, exactly one of the two players has a winning strategy. In the learning game of the previous definition, the adversary has a winning strategy if and only if $H$ has an infinite Littlestone tree; otherwise the learner has a winning strategy, which can be chosen to be universally measurable under the measurability assumptions on $H$ used by Bousquet, Hanneke, Moran, van Handel and Yehudayoff.

## Proof sketch

Determinacy of open games is the Gale–Stewart theorem: if the open player has no winning strategy, the other player keeps the play inside positions from which the open player still has no winning strategy, which is possible move by move, and this avoids every winning finite prefix forever. A winning adversary strategy in the learning game unfolds into an infinite tree of realizable points indexed by the learner's predictions, which is exactly an infinite Littlestone tree; conversely an infinite Littlestone tree is a winning strategy for the adversary. Measurability of the learner's strategy uses an ordinal-valued rank of positions, which is a measurable function under the source's assumptions.

## Depends on

- [Gale–Stewart games for learning](gale-stewart-games.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
