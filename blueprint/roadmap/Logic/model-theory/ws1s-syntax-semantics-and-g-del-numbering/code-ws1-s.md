# Code WS1 S

Gödel numbering of WS1S formulas by Cantor pairing with a disjoint tag per constructor: every code is `Nat.pair tag payload`, with tags `0` (equality), `1` (less than), `2` (membership), `3` (falsum), `4` (implication), `5` (first-order universal quantification) and `6` (second-order universal quantification). In particular falsum is coded by `Nat.pair 3 0`, not by the bare constant `3`, which would collide with the code of a less-than formula since `Nat.pair 1 1 = 3`.
