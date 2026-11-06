# FLM Monster finite-group construction

This Autoform blueprint plans the finite-group work in
Frenkel–Lepowsky–Meurman's *Vertex Operator Algebras and the Monster* (1988).
It is a coarse roadmap for review. The [six Lean milestone declarations](../Milestones.lean)
have `sorry` proof bodies and [documented construction gaps](../GAPS.md).
No proofs are complete, and the detailed FLM passages still need source verification.

## Read in order

- [Roadmap preface](roadmap/README.md)
- [1. The local subgroup](roadmap/local-subgroup/README.md)
- [2. The extra FLM symmetry](roadmap/extra-symmetry/README.md)
- [3. Identifying the Monster](roadmap/monster-identification/README.md)
- [Coverage contract](coverage/README.md)

## Source and implementation evidence

- [Adopted reference and passage checklist](sources/flm.md)
- [Pinned library audit](sources/library-audit.md)
- [Project-authored scope and external interfaces](sources/scope.md)

The chapter dependencies express coarse mathematical prerequisites. There are
no declaration-sized proof tasks yet. Review the roadmap and coverage contract
before expanding them into a source-grounded theorem DAG.

For introductory terminology and entry tasks, see the
[textbook README](../README.md).
Use the [minimal milestone theorem statements](../HUMAN_REVIEW.md) to review
the mathematical endpoints without reading the full infrastructure graph.
