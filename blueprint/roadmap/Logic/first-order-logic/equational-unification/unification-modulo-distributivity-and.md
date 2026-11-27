# Unification with constants modulo distributivity and associativity is undecidable

No algorithm decides unifiability of unification problems with constants modulo the theory that makes one binary symbol distribute on both sides over a second, associative, binary symbol.

**Theorem (Szabó; Siekmann and Szabó).** Let $f$ and $g$ be binary function symbols. $(D_{f,g} \cup A_g)$-unification with constants is undecidable: there is no algorithm that decides, for an [E-unification problem](equational-unification-problems.md) with constants modulo $D_{f,g} \cup A_g$, whether it is unifiable. Here $D_{f,g}$ states that $f$ distributes over $g$ from the left and from the right, and $A_g$ states that $g$ is associative.

Without associativity the problem becomes decidable: $D_{f,g}$-unification with constants is decidable (Schmidt-Schauß), and $D^l_{f,g}$-unification with constants is decidable in polynomial time (Tidén and Arnborg).

## Depends on

- [E-unification problems](equational-unification-problems.md)

## Proof depends on

None.

## Expansion

The source reports the result without proof; the original proof is in Szabó's 1982 thesis and in the journal paper of Siekmann and Szabó. Tidén and Arnborg later strengthened it to every equational theory above $D_{f,g} \cup A_g$ that is consistent with Peano arithmetic.

## Sources

- J. Siekmann and P. Szabó, "The undecidability of the $D_A$-unification problem", *Journal of Symbolic Logic* 54(2):402–414, 1989, doi:10.2307/2274856 (original source, cited beside the copy read).
- F. Baader and W. Snyder, "Unification theory", in A. Robinson and A. Voronkov (eds.), *Handbook of Automated Reasoning*, Vol. I, Elsevier, 2001, Chapter 8, pp. 445–533, doi:10.1016/B978-044450813-3/50010-2; read in the authors' open-access copy at <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSnyderHandbook.pdf>: Section 3.4, paragraph on distributivity, which states the undecidability and the decidable cases.
