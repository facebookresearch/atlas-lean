# Reachability for hierarchical pi-calculus terms is undecidable

Reachability of a given term remains undecidable for hierarchical π-calculus terms, even for those certified by the hierarchical type system, although their coverability problem is decidable.

**Theorem.** The reachability problem (given $P$ and $Q$, is a term structurally congruent to $Q$ reachable from $P$?) is undecidable for [hierarchical terms](hierarchical-pi-calculus-terms.md) $P$, and already for $P$ typably hierarchical.

## Depends on

- [Hierarchical terms of the pi-calculus](hierarchical-pi-calculus-terms.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from reachability of Minsky (two-counter) machines, through a *weak* encoding: not every run of the encoded term represents a real run of the machine. Reachability of an exact target term, unlike coverability, distinguishes the reachable terms that encode reachable configurations from the others, so the machine reaches its target configuration iff the encoding reaches the corresponding term. The encoding is typably hierarchical.

The result separates the fragment from models such as Petri nets, whose reachability is decidable, and from $\mathrm{CCS}^!$, which is contained in it and has decidable reachability. Coverability (reaching a term into which a given query embeds) is decidable for depth-bounded and hence for hierarchical terms, which suffices for many safety properties.

## Sources

- Emanuele D'Osualdo and C.-H. Luke Ong, "On Hierarchical Communication Topologies in the π-calculus", in *Programming Languages and Systems (ESOP 2016)*, Lecture Notes in Computer Science 9632, Springer, 2016, pp. 149–175, <https://doi.org/10.1007/978-3-662-49498-1_7>; read as arXiv:1601.01725v2, <https://arxiv.org/abs/1601.01725v2>: Theorem 8 in Section 7.1 ("Expressivity") and the encoding of Minsky machines in the appendix, in the numbering of that version.
