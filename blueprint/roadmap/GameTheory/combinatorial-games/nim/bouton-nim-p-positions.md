# Bouton's move properties in Nim

Let a Nim position be a finite list of heap sizes
$a_1, \dots, a_n \in \mathbb{N}$, with nim-sum $a_1 \oplus \cdots \oplus a_n$, where $\oplus$
is bitwise exclusive or and the empty list has nim-sum $0$. A move chooses an index $i$ and
replaces $a_i$ by a natural number $y < a_i$. Then: (i) if the position has nim-sum $0$, every
move leads to a position with nonzero nim-sum; (ii) if the position has nonzero nim-sum, some
move leads to a position with nim-sum $0$.

Positions with no move (the empty list and the all-zero lists) have nim-sum $0$, so the two
properties determine the normal-play labelling by induction on the game: the positions with
nim-sum $0$ are exactly the P-positions (previous player wins) and the others are the
N-positions.

## Sources

- Tanya Khovanova and Joshua Xiong, "Nim Fractals", Journal of Integer Sequences 17 (2014), theorem lines 155–159, https://cs.uwaterloo.ca/journals/JIS/VOL17/Khovanova/khova6.tex complete-source SHA-256 `6f8be9d461ff98b5a7c878830eb169e69ba8dd7540948d9149527fdb5ca7783a`, normalized theorem lines 157–159 SHA-256 `d0cc29c58096c58f4d34f2b9e3d199a1316f13e98b5170e9c316c5385ce6e43f`. Proves `Wanted` entry `bouton_nim_p_positions`.
