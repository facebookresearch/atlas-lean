# The measure L is at most the encoding size

For every linear program with integer data $A$, $b$, $c$, the measure $L$ of [the encoding size page](encoding-size-of-a-linear-program.md) satisfies $L < \mathrm{size}(LP)$. Hence an algorithm whose running time is polynomial in $L$ runs in time polynomial in the encoding size of its input.

## Depends on

- [Encoding size of a linear program](encoding-size-of-a-linear-program.md)

## Sources

- M. X. Goemans, *Linear Programming*, lecture notes for 18.415/6.854 Advanced Algorithms, MIT, October 1994, <https://www.cs.cmu.edu/afs/cs/user/glmiller/public/Scientific-Computing/F-11/RelatedWork/Goemans-LP-notes.pdf>, Section 11.1, Proposition 13 and the lemma before its proof.
