# Code WS1 STerm

Gödel numbering of WS1S terms by Cantor pairing with a disjoint tag per constructor: every code is `Nat.pair tag payload`, with tag `0` for variables, `1` for the constant `0`, and `2` for successor. Bare constants are never used as codes: for instance coding `0` by the bare number `1` would collide with the code `Nat.pair 0 1 = 1` of variable `1`.
