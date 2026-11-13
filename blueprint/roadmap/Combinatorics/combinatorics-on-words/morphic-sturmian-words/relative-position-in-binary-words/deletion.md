# The deletion operator

For an infinite word $w$ over the letters $a$ and $b$, the word
$D(w)$ is $D_a(D_b(w))$, where $D_\alpha$ deletes the first occurrence of the letter $\alpha$
(and deletes the first letter of a word in which $\alpha$ does not occur): first apply $D_b$,
then $D_a$. When both letters occur in $w$, $D(w)$ is $w$ with its first $b$ and its first $a$
deleted.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2 (definition of the deletion operator `D`).
