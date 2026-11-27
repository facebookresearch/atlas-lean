# Unification with constants modulo an endomorphism of an AC symbol is undecidable

When a unary symbol acts as an endomorphism of an associative and commutative binary symbol, with or without a unit, solvability of unification problems with constants is undecidable.

**Theorem (Narendran).** Let $g$ be a binary function symbol, $h$ a unary function symbol and $e$ a constant. For each of the theories

$$
\mathrm{End}_{h,g} \cup AC_g \qquad \text{and} \qquad \mathrm{End}_{h,g} \cup \mathrm{End}_{h,e} \cup ACU_g,
$$

solvability of [E-unification problems](equational-unification-problems.md) with constants is undecidable. Here $\mathrm{End}_{h,g}$ states $h(g(x,y)) \approx g(h(x), h(y))$, $\mathrm{End}_{h,e}$ states $h(e) \approx e$, $AC_g$ makes $g$ associative and commutative, and $ACU_g$ adds $e$ as a unit of $g$.

By contrast, solvability of unification problems with constants is decidable for $\mathrm{End}_{h,g}$ alone (Vogel) and, when $g$ is also idempotent, for $\mathrm{End}_{h,g} \cup \mathrm{End}_{h,e} \cup ACUI_g$, where it is EXPTIME-complete (Baader and Narendran).

## Depends on

- [E-unification problems](equational-unification-problems.md)

## Proof depends on

None.

## Expansion

As the title of the original paper indicates, the proof goes through linear equations over polynomial semirings: modulo these theories, unification problems with constants amount to systems of linear equations whose coefficients are polynomials in $h$ with natural-number coefficients, and solvability of such systems is undecidable.

## Sources

- P. Narendran, "Solving linear equations over polynomial semirings", in *Proceedings of the 11th Annual IEEE Symposium on Logic in Computer Science (LICS 1996)*, IEEE Computer Society, 1996, pp. 466–472, doi:10.1109/LICS.1996.561463 (original source, cited beside the copy read).
- F. Baader and W. Snyder, "Unification theory", in A. Robinson and A. Voronkov (eds.), *Handbook of Automated Reasoning*, Vol. I, Elsevier, 2001, Chapter 8, pp. 445–533, doi:10.1016/B978-044450813-3/50010-2; read in the authors' open-access copy at <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSnyderHandbook.pdf>: Section 3.4, paragraph "Endomorphisms", which states the undecidability for both theories and the decidable cases.
