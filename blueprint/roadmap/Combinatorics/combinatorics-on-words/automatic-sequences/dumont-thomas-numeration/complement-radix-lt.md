# The complement radix order

For finite words $w$ and $w'$ over $\mathbb{N}$, write
$|w|$ for the length of $w$. Then $w \prec w'$ holds exactly in the following three cases:
$w$ starts with $1$ and $w'$ starts with $0$; both words start with $0$, and either
$|w| < |w'|$, or $|w| = |w'|$ and $w$ is lexicographically smaller than $w'$ (radix order);
both words start with $1$, and either $|w| > |w'|$, or $|w| = |w'|$ and $w$ is
lexicographically smaller than $w'$ (reversed radix order). In particular, a word that does
not start with $0$ or $1$ is never related to any word.

On the words starting with $0$ or $1$ this is the order $\prec$ of the paper.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 8 (definition of the total order `≺`).
