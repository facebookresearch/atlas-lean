# Unification is undecidable for every theory above distributivity and associativity consistent with arithmetic

Every equational theory that contains two-sided distributivity with associativity, or left distributivity with a unit and associativity, and that is consistent with Peano arithmetic has an undecidable unification problem.

**Theorem (Tidén and Arnborg).** Let $f$ and $g$ be binary function symbols and $e$ a constant, and let $E$ be an equational theory that lies above $D_{f,g} \cup A_g$ or above $D^l_{f,g} \cup U_f \cup A_g$, that is, every identity of one of these theories holds modulo $E$ (see [E-unification problems](equational-unification-problems.md) for the theories). If $E$ is consistent with Peano arithmetic when $f$ is read as multiplication, $g$ as addition and $e$ as $1$, then $E$ has an undecidable unification problem.

In contrast, $D^l_{f,g}$-unification with constants is decidable in polynomial time (Tidén and Arnborg), and $(D^l_{f,g} \cup U_f)$-unification with constants is decidable (Schmidt-Schauß); the source reports decidability of $(D_{f,g} \cup U_f)$-unification as open.

## Depends on

- [E-unification problems](equational-unification-problems.md)
- [Peano arithmetic](../peano-arithmetic-and-robinson-s-q/patheory.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The copy read states the theorem without proof; the original proof is in Tidén and Arnborg and is not reproduced here. The consistency hypothesis refers to reading $f$ as multiplication, $g$ as addition and $e$ as $1$. The result strengthens the undecidability of $(D_{f,g} \cup A_g)$-unification with constants due to Szabó and to Siekmann and Szabó.

## Sources

- E. Tidén and S. Arnborg, "Unification problems with one-sided distributivity", *Journal of Symbolic Computation* 3(1–2):183–202, 1987, doi:10.1016/S0747-7171(87)80026-3 (original source, cited beside the copy read).
- F. Baader and W. Snyder, "Unification theory", in A. Robinson and A. Voronkov (eds.), *Handbook of Automated Reasoning*, Vol. I, Elsevier, 2001, Chapter 8, pp. 445–533, doi:10.1016/B978-044450813-3/50010-2; read in the authors' open-access copy at <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSnyderHandbook.pdf>: Section 3.4, paragraph on distributivity, which states the theorem in this form.
