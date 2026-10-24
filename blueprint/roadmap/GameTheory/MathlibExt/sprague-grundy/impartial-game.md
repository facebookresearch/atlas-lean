---
article_id: af_75295bb510bb9c5b1839983b
declaration: structure
origin: cited
statement: formalized
lean: MetaMathlibExt.SpragueGrundy.ImpartialGame
---

# Impartial Game

Finite impartial game with a strictly decreasing natural rank.

Finite move sets plus a strictly decreasing natural rank give a finite
reachable game tree from any starting position, even if `Pos` contains
unreachable points: every move strictly decreases `rank`, so every play
terminates and only finitely many positions are reachable.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GameTheory.SpragueGrundy](../../../../sources/v2/MathlibExt.md)
