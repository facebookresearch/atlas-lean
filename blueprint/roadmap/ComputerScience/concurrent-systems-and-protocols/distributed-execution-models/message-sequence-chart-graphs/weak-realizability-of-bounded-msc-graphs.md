# Weak realizability of bounded MSC graphs is undecidable

It is undecidable whether a bounded MSC graph is weakly realizable, that is, whether its set of scenarios is closed under the scenarios that every distributed implementation must also produce, although the same question is coNP-complete for finite sets of MSCs.

**Theorem (Alur, Etessami and Yannakakis).** Given a bounded [MSC graph](msc-graphs-and-weak-realizability.md) $G$, it is undecidable whether $G$ is weakly realizable, that is, whether $L(G) = L^w(G)$ (Theorem 1).

The graph is the input. For a finite set of MSCs weak realizability is coNP-complete, and safe realizability of bounded MSC graphs is decidable.

## Depends on

- [MSC graphs and weak realizability](msc-graphs-and-weak-realizability.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The reduction is from a variant of the Post correspondence problem. Inspecting the standard proof of undecidability of PCP shows that the one-sided version, where one string never overtakes the other, remains undecidable, and a further variant, the relaxed PCP (choose from either list at each index, at least once differently, with the prefix condition), is shown undecidable by a homomorphic encoding (Lemma 2). From an instance one builds a bounded MSC graph with four processes in which an implied but unspecified MSC exists iff the instance has a solution.

## Sources

- Rajeev Alur, Kousha Etessami and Mihalis Yannakakis, "Realizability and verification of MSC graphs", *Theoretical Computer Science* 331(1):97–114, 2005, doi:10.1016/j.tcs.2004.09.034; read in the authors' open-access copy at <https://www.cis.upenn.edu/~alur/Icalp01.pdf>, which carries the journal text: Theorem 1, Lemma 2 and their proofs in Section 3.1 of that copy.
