# Cyclic shift strategy

A strategy assigns to each $m$ a permutation of $m$ positions, used
to rearrange the entries on the $m$ incorrect positions of a guess. The cyclic shift strategy
$\mathrm{CS}$ has component $\mathrm{CS}[m] = [2, 3, \dots, m, 1]$ in one-line notation, that is,
the rotation $i \mapsto i + 1 \pmod m$ of $\{0, 1, \dots, m-1\}$.

## Sources

- Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29 (2026), Article 26.1.7, Section 2.
