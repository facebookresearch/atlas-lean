# The Dershowitz–Manna multiset ordering is well-founded

Let $\alpha$ be a preordered set whose strict order $<$ is well-founded. On finite multisets over $\alpha$, let $M < N$ hold if there are finite multisets $X$, $Y$ and $Z$ with $Z \ne \emptyset$, $M = X + Y$, $N = X + Z$, and for every $y \in Y$ some $z \in Z$ with $y < z$ (the Dershowitz–Manna ordering). Then this relation is well-founded.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 1.4, Theorem 1.10 (c), p. 9, with the proof referred to F. Baader and T. Nipkow, *Term Rewriting and All That*, Cambridge University Press, 1998, pp. 22–24; the ordering is due to N. Dershowitz and Z. Manna (1979).
- Mathlib, `Multiset.wellFounded_isDershowitzMannaLT` in `Mathlib/Data/Multiset/DershowitzManna.lean`.
