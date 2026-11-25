# Berge's lemma

A matching is maximum exactly when it admits no augmenting path (Berge, 1957). Hopcroft and Karp (1973) sharpened this for arbitrary graphs: a matching $N$ larger than $M$ yields $|N| - |M|$ disjoint $M$-augmenting paths, so short augmenting paths exist, and augmenting along a shortest path never creates a shorter one. These facts drive their phase bound.

- [Augmenting path](is-augmenting-walk.md)
- [Berge's lemma](berge.md)
- [Berge's lemma for matching subgraphs](berge-general.md)
- [Berge's lemma with augmenting walks](berge-iff-not-exists-is-augmenting-walk.md)
- [Augmenting along a path (Hopcroft–Karp, Lemma 1)](symm-diff-is-matching.md)
- [Disjoint augmenting paths in a symmetric difference (Hopcroft–Karp, Theorem 1)](exists-disjoint-augmenting-walks.md)
- [A short augmenting path exists (Hopcroft–Karp, Corollary 2)](exists-is-augmenting-walk-length-le.md)
- [Augmenting after a shortest augmentation (Hopcroft–Karp, Theorem 2)](length-add-card-inter-le.md)

## Related topics

- [Maximum bipartite matching](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/README.md): the augmenting-path and Hopcroft–Karp algorithms in bipartite graphs, proved correct with the $2\lfloor\sqrt{b}\rfloor + 2$ phase bound.
- [Matching in general graphs](../../../TheoryOfComputation/polynomial-time-problems/matching-in-general-graphs/README.md): Edmonds' blossom algorithm finds augmenting paths in nonbipartite graphs in polynomial time.
