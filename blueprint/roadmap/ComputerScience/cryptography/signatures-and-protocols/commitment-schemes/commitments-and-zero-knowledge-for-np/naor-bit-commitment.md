# Naor's bit commitment from a pseudorandom generator

Let $G$ stretch $n$ bits to $3n$ bits. In *Naor's commitment*, the receiver sends a uniform $R \in \{0,1\}^{3n}$; to commit to a bit $b$ the sender picks a uniform seed $s$ and sends $c = G(s)$ if $b = 0$ and $c = G(s) \oplus R$ if $b = 1$; to open it reveals $(b, s)$ and the receiver checks the corresponding equation.

## Depends on

- [Asymptotic PRG security relative to a class of distinguishers](../../../symmetric-key/pseudorandom-generators/prgsecure.md)
- [The binding experiment](../the-computational-binding-game-for-keyed-commitm/binding-game.md)

## Sources

- M. Naor, "Bit Commitment Using Pseudorandomness", Journal of Cryptology 4(2), 1991.
