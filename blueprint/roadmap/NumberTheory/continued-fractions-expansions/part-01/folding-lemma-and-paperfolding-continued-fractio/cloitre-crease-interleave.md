# Interleaving creases into a Cloitre word

Given a sequence $c : \mathbb{N} \to \mathbb{N}$
and a start index $j$, the crease interleaving of a finite word $w$ of natural numbers reads $w$
from left to right as letters $(2)$ and $(1, 1)$ and inserts $c_j, c_{j+1}, c_{j+2}, \dots$ after
the successive letters. Precisely, the empty word gives the empty word; a word $2, w'$ gives
$2, c_j$ followed by the interleaving of $w'$ from index $j + 1$; a word $1, 1, w'$ gives
$1, 1, c_j$ followed by the interleaving of $w'$ from index $j + 1$; and any other nonempty word
$a, w'$ gives $a$ followed by the interleaving of $w'$ from the same index $j$.

The last case is unreachable on the approximants $A_k$ of Cloitre's sequence.

## Sources

- Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 14 (Cloitre's sequence occurs one `[1, 1]` or `[2]` at a time, interleaved with crease terms).
