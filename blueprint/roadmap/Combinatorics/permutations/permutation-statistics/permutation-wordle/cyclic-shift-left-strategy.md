# Cyclic shift left strategy

For $n \in \mathbb{N}$, the strategy $\mathrm{CSL}_n$ assigns
to each $m$ a permutation of $m$ positions: for $m = n$ the left cyclic shift
$[m, 1, 2, \dots, m-1]$ in one-line notation, that is, $i \mapsto i - 1 \pmod m$, and for every
$m \ne n$ the right cyclic shift $[2, 3, \dots, m, 1]$, that is, $i \mapsto i + 1 \pmod m$.

## Sources

- Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29 (2026), Article 26.1.7, Section 4.3.
