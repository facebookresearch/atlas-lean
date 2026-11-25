# Fuelled parsing of LTL tokens

Reads one formula from the front of a token list and returns it with the remaining tokens, or
fails if the fuel runs out or no formula can be read. On the tokens of the
[token encoding](tokens.md), $\langle 0, a\rangle$ reads as the atom $a$, and $\langle k, 0\rangle$
for $k$ equal to $1$, $2$, $3$, $4$ or $5$ reads as truth, negation, conjunction, next or until,
followed by its arguments.
