---
article_id: af_283d3adad451496ef39721d0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.BoutonNim.bouton_nim_p_positions
---

# Bouton Nim

Bouton's characterization of normal-play Nim P-positions as nim-sum-zero positions.

A position is a finite list `pos : List ℕ` of heap sizes, its nim-sum is
`List.foldl Nat.xor 0 pos`, and a legal move chooses an index `i : Fin pos.length`
and replaces the heap `pos.get i` by a strictly smaller `y : ℕ`, giving
`pos.set i.val y`. The conjunction below states the two characteristic move
properties of P-positions (previous-player-win positions): (i) from a nim-sum-zero
position every legal move reaches a nim-sum-nonzero position, i.e. no move stays
inside the zero class and all options of a P-position are N-positions; (ii) from a
nim-sum-nonzero position some legal move reaches a nim-sum-zero position, i.e. every
N-position has a move into the zero class. These two clauses are exactly the
inductive definition of the P/N partition: the terminal positions — the empty list
and the all-zero lists, which have nim-sum `0` and admit no legal move since
`y < 0` is impossible (respectively there is no index at all) — satisfy the first
clause vacuously while the second clause is inapplicable, so terminals are
P-positions, matching the normal-play rule that a player with no move loses; the two
clauses then fix the P/N labelling uniquely by induction on the game graph. Hence
the zero-nim-sum positions are precisely the P-positions.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GameTheory.BoutonNim](../../../sources/v2/MathlibExt.md)
- Tanya Khovanova and Joshua Xiong, "Nim Fractals", Journal of Integer Sequences 17 (2014), theorem lines 155–159, https://cs.uwaterloo.ca/journals/JIS/VOL17/Khovanova/khova6.tex complete-source SHA-256 `6f8be9d461ff98b5a7c878830eb169e69ba8dd7540948d9149527fdb5ca7783a`, normalized theorem lines 157–159 SHA-256 `d0cc29c58096c58f4d34f2b9e3d199a1316f13e98b5170e9c316c5385ce6e43f`. Proves `Wanted` entry `bouton_nim_p_positions`.
