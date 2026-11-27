# Membership in the hierarchical fragment of the pi-calculus is undecidable

Whether a π-calculus term is hierarchical, that is, whether some finite hierarchy is an invariant of the shape of all its reachable terms, is undecidable.

**Theorem.** There is no algorithm that decides, given an arbitrary π-calculus term $P$, whether $P$ is [hierarchical](hierarchical-pi-calculus-terms.md).

## Depends on

- [Hierarchical terms of the pi-calculus](hierarchical-pi-calculus-terms.md)

## Proof depends on

None.

## Expansion

The π-calculus is Turing-complete, so termination of π-calculus terms is undecidable. Termination is decidable for depth-bounded terms, hence for hierarchical ones. The source also proves that every terminating term is hierarchical, since its finitely many reachable terms can be annotated along a total order of their active names. A decision procedure for being hierarchical would then decide termination: a term that is not hierarchical does not terminate, and for a hierarchical term termination can be decided. The argument adapts Meyer's proof that being depth-bounded is undecidable.

This is an obstacle to using the fragment directly, since membership has to be established by hand; the source's type system gives a sufficient, decidable criterion (typably hierarchical terms) instead.

## Sources

- Emanuele D'Osualdo and C.-H. Luke Ong, "On Hierarchical Communication Topologies in the π-calculus", in *Programming Languages and Systems (ESOP 2016)*, Lecture Notes in Computer Science 9632, Springer, 2016, pp. 149–175, <https://doi.org/10.1007/978-3-662-49498-1_7>; read as arXiv:1601.01725v2, <https://arxiv.org/abs/1601.01725v2>: the undecidability theorem for membership in Section 3, the lemma that terminating terms are hierarchical, and the decidability of termination for depth-bounded terms cited in Section 2, of that version.
