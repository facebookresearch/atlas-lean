# Adachi: stable matchings are the fixed points of a monotone operator

A pre-matching is a fixed point of Adachi's operator $T$ if and only if it is (the pre-matching of) a stable matching. By Tarski's fixed-point theorem the fixed points form a complete lattice; its greatest element is the proposer-optimal stable matching produced by proposer-proposing deferred acceptance, and its least element is the receiver-optimal stable matching.

## Proof sketch

At a fixed point, mutual favourites give a consistent matching, and the absence of a blocking pair is exactly the fixed-point condition. Iterating $T$ from the top element mimics deferred acceptance.

## Depends on

- [Pre-matchings and Adachi's operator](adachi-pre-matching-operator.md)
- [Gale–Shapley theorem](../stable-marriage-problem/gale-shapley-exists-stable-matching.md)

## Proof depends on

- [The men's join of two stable matchings is stable](../../../GameTheory/matching-markets/lattice-of-stable-matchings/is-stable-men-join.md)

## Sources

- H. Adachi, "On a Characterization of Stable Matchings", Economics Letters 68(1), 2000.
- J. Schummer and R. V. Vohra, "Mechanism Design without Money", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
