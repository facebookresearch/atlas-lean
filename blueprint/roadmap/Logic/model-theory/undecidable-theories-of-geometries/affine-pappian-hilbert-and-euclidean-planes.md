# Affine, Pappian, Hilbert and Euclidean planes have undecidable theories

The first-order theories of affine planes and of Pappian planes are undecidable, and so are the sets of first-order consequences of Hilbert's axioms for plane geometry, with or without the parallel axiom, and of the axioms of Euclidean planes.

**Axiom systems.** Plane geometries are two-sorted structures of points and lines with an incidence relation, possibly with betweenness and congruence. An *affine plane* satisfies the incidence axioms (two distinct points lie on a unique line, every line has two points, three non-collinear points exist), the parallel axiom (through a point there is at most one line missing a given line) and an infinite scheme saying that no line has finitely many points; a *Pappian plane* also satisfies Pappus' axiom. A *Hilbert plane* satisfies Hilbert's incidence, betweenness (including Pasch's axiom) and congruence axioms, a *P-Hilbert plane* is a Hilbert plane satisfying the parallel axiom, and a *Euclidean plane* is a P-Hilbert plane satisfying the circle–circle intersection axiom: two circles intersect if one has a point inside and a point outside the other. The *consequence problem* of a set of axioms asks whether a given first-order sentence follows from it.

**Theorem (Makowsky).**

1. The first-order theories of Pappian planes and of affine planes are undecidable (Theorem 1).
2. The consequence problems for P-Hilbert planes, for Hilbert planes and for Euclidean planes are undecidable (Theorem 12).

In each case the real plane is a model, while the complete first-order theory of the real plane, Tarski's elementary geometry, is decidable. The same method gives undecidability for Wu's metric geometry and for ordered origami planes; see [metric Wu planes](finite-extensions-of-metric-wu-plane-geometry.md) and [ordered origami planes](theory-of-ordered-origami-planes-is-undecidable.md).

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Finite subtheories of the theory of the real field are undecidable](finite-subtheories-of-the-real-field-are.md)

## Expansion

Coordinatization makes the geometries interchangeable with fields by first-order translation schemes: a Pappian plane with no finite lines is the affine plane over a field of characteristic $0$ (Artin, with Szmielew's form of the converse), a P-Hilbert plane is the plane over an ordered Pythagorean field obtained from its segment arithmetic, and a Euclidean plane is the plane over a Euclidean field (Hartshorne). Part 1 transfers Julia Robinson's undecidability of the theory of fields of characteristic $0$, which rests on defining the integers in the rationals; the affine case follows since Pappus' axiom is a single extra sentence. Part 2 applies Ziegler's theorem that every finite set of field axioms true in the reals has an undecidable set of consequences, together with the fact that the field recovered from the plane over a Pythagorean field is that field again; dropping the parallel axiom keeps undecidability because only one axiom is removed. A good expansion links pages for Artin's coordinatization of Pappian planes, Hartshorne's segment-arithmetic theorems and Julia Robinson's undecidability of the theory of fields of characteristic $0$ (through the undecidability of the first-order theory of the rationals).

## Sources

- J. A. Makowsky, "Can one design a geometry engine? On the (un)decidability of certain affine Euclidean geometries", *Annals of Mathematics and Artificial Intelligence* 85(2–4), pp. 259–291, 2018, doi:[10.1007/s10472-018-9610-1](https://doi.org/10.1007/s10472-018-9610-1); read in arXiv:1712.07474v3 ([arXiv](https://arxiv.org/abs/1712.07474v3)), whose numbering is used: the axiom systems of Section 3, Propositions 1 and 2 (Artin's coordinatization; Julia Robinson), Theorem 1 (affine and Pappian planes), Theorem 2 (Ziegler), Theorems 7–9 and Corollary 2 (segment arithmetic), and Theorem 12 (Hilbert and Euclidean planes) in Section 6.2.
