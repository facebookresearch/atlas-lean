# Lattice of stable matchings

For two stable matchings of a marriage market, giving every man the partner he prefers among his two partners yields again a stable perfect matching, in which every woman receives the partner she likes less. Roth (1986, Lemma 2) proves the college-admissions version of this observation, uses it for the rural hospitals theorem, and attributes the marriage case to Conway as reported by Knuth (*Mariages stables*, 1976); this is the property that makes the set of stable matchings a lattice under the men's common order. This topic covers the join and the opposition of interests in the marriage model with complete preference lists. The join also gives a proof of optimality that does not follow the algorithm: a stable matching minimising a potential is unchanged by the men's join with any stable matching, so it is man-optimal; the existence of some stable matching is taken from the Gale–Shapley theorem, whose proof runs deferred acceptance. The women's join is the same construction with the sides exchanged.

## The join and its stability

- [Men's pointwise best partner](men-join-fun.md)
- [The men's best partner is one of the two partners](men-join-fun-eq-or.md)
- [No man prefers his first partner to the join](not-lt-men-join-fun-left.md)
- [No man prefers his second partner to the join](not-lt-men-join-fun-right.md)
- [Preferred to the join, preferred to the first partner](lt-left-of-lt-men-join-fun.md)
- [Preferred to the join, preferred to the second partner](lt-right-of-lt-men-join-fun.md)
- [The men's join of two stable matchings is injective](men-join-fun-injective.md)
- [Men's join of two stable matchings](men-join.md)
- [Each man's join partner is his preferred partner](men-join-apply.md)
- [The men's join of two stable matchings is stable](is-stable-men-join.md)

## Opposition of interests

- [Each woman's partner in the men's join is one of her two partners](men-join-symm-eq-or.md)
- [Opposition of interests: no woman prefers her men's-join partner to her first partner](not-lt-men-join-symm-left.md)
- [Opposition of interests: no woman prefers her men's-join partner to her second partner](not-lt-men-join-symm-right.md)

## The man-optimal stable matching

- [Existence of a man-optimal stable matching, through the men's join](exists-stable-forall-not-lt.md)

## Related topics

- [Stable marriage problem](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/README.md): the model and the existence of stable matchings.
- [Stable matching mechanisms and incentives](../stable-matching-mechanisms-and-incentives/README.md): Roth's market, whose two stable matchings $x$ and $y$ have men's join $x$, is the test case of these pages.
- [Rural hospitals theorem](../rural-hospitals-theorem/README.md): Roth (1986) combines the join (his Lemma 2) with the invariance of the number of positions filled (his Lemma 1) to prove the rural hospitals theorem.
