# Maximum bipartite matching

- [Matching in a bipartite graph](is-matching.md)
- [Matched pairs of a partner assignment](pairs.md)
- [Partner arrays that describe a matching](valid.md)
- [Unmatched left vertex](free.md)
- [Alternating breadth-first layers](layers.md)
- [Matched reached left vertices are reached through a partner](exists-mate-of-mem-layers.md)
- [The left layers stop growing once two consecutive ones agree](layers-fst-eq-of-eq.md)
- [Rounds $a$ and $a + 1$ reach the same left vertices](layers-fst-stable.md)

## Augmenting paths

- [Walking the layers back](path-to.md)
- [Flipping a list of pairs](flip.md)
- [Alternating path](alt-path.md)
- [Augmenting path](is-augmenting-path.md)
- [The walk back is an alternating path](path-to-spec.md)
- [Flipping an alternating path keeps a matching](valid-flip.md)
- [Matched right vertices](matched.md)
- [Flipping an alternating path matches its first vertex](matched-flip.md)
- [The walk back from an unmatched reached vertex is an augmenting path](path-to-is-augmenting-path.md)
- [Flipping an augmenting path adds one matched vertex](card-matched-flip.md)

## The algorithm

- [One augmentation step](augment.md)
- [Augmentation loop](max-matching-aux.md)
- [The augmenting-path maximum matching](max-matching.md)
- [Matched pairs and matched right vertices are equinumerous](card-pairs.md)
- [A valid partner array gives a matching](is-matching-pairs.md)
- [A successful augmentation grows the matching by one edge](augment-some.md)
- [A failed augmentation reaches no unmatched right vertex](augment-none.md)
- [Kőnig's certificate](card-le-of-no-free.md)
- [Enough augmentations reach a maximum matching](max-matching-aux-spec.md)
- [The augmenting-path algorithm returns a matching](is-matching-max-matching.md)
- [Optimality of the augmenting-path matching algorithm](card-le-max-matching.md)

## Hopcroft–Karp phases

- [Partner of a left vertex](partner-of.md)
- [Marking a right vertex dead](mark-dead.md)
- [Trying the candidate predecessors of a right vertex](try-preds.md)
- [Depth-first search of a Hopcroft–Karp phase](search-path.md)
- [Trying candidates keeps dead vertices dead](try-preds-mono.md)
- [A path found by trying candidates comes from one candidate](try-preds-some.md)
- [When trying candidates finds a path](try-preds-is-some.md)
- [The dead set of a search only grows](search-path-mono.md)
- [Search paths are alternating paths through unused vertices](search-path-spec.md)
- [Searches from reached vertices succeed when nothing is used or dead](search-path-is-some.md)
- [Marking the left vertices of a path used](mark-l.md)
- [Marking the right vertices of a path used](mark-r.md)
- [Phase search over candidates](phase-aux.md)
- [First free round](first-free-round.md)
- [Hopcroft–Karp phase](phase.md)
- [Hopcroft–Karp step](hk-step.md)
- [Hopcroft–Karp phase loop](hopcroft-karp-aux.md)
- [Hopcroft–Karp](hopcroft-karp.md)
- [Characterization of the first free round](first-free-round-eq-some.md)
- [When there is no first free round](first-free-round-eq-none.md)
- [Phase paths are disjoint augmenting paths](phase-aux-spec.md)
- [Flipping disjoint alternating paths at once keeps a matching](valid-flip-flatten.md)
- [Flipping disjoint augmenting paths matches at least one more vertex](card-matched-flip-flatten.md)
- [A phase finds a path when an unmatched right vertex is reached](phase-ne-nil.md)
- [A successful Hopcroft–Karp step grows the matching](hk-step-some.md)
- [A Hopcroft–Karp step that finds nothing](hk-step-none.md)
- [Correctness of the phase loop](hopcroft-karp-aux-spec.md)
- [Hopcroft–Karp returns a matching](is-matching-hopcroft-karp.md)
- [Correctness of Hopcroft–Karp](card-le-hopcroft-karp.md)

## Phases use shortest augmenting paths

- [The start of an alternating chain of $L$ pairs is reached within $L$ rounds](mem-layers-length.md)
- [No augmenting path is shorter than a phase's](le-length-of-is-augmenting-path.md)
- [Length bound for search paths](search-path-length-le.md)
- [Length bound for phase paths](phase-aux-length-le.md)
- [Phases use shortest augmenting paths](length-of-mem-phase.md)

## Phases find maximal sets of shortest augmenting paths

- [Exact level of a right vertex](exact-level.md)
- [Alternating chain to an unmatched left vertex](is-chain-from.md)
- [No shortest escape](no-escape.md)
- [The second pair of a shortest alternating chain](tail.md)
- [Partners of predecessors lie one level earlier](partner.md)
- [Where newly dead vertices come from](try-preds-dead.md)
- [When trying candidates fails](try-preds-none.md)
- [A failed search marks its start dead](search-path-none-marks.md)
- [Dead vertices have no escape](search-path-dead.md)
- [Shortest chains avoiding earlier paths contain no dead vertex](not-dead-of-chain.md)
- [Invariant of a phase](phase-aux-maximal.md)
- [Phases are maximal](phase-maximal.md)

## Distances do not decrease across a phase

- [A matched right vertex is reached no later than its partner](mem-layers-snd-of-mate.md)
- [Levels along a shortest alternating chain](pair-levels-of-chain.md)
- [Levels of the pairs of a phase](pair-levels-of-mem-phase.md)
- [A phase leaves no new unmatched left vertex](free-of-free-flip.md)
- [Distances do not decrease across a phase](layers-flip-phase-subset.md)
- [The first free round does not decrease across a phase](le-first-free-round-flip-phase.md)
- [The paths of a phase are vertex-disjoint augmenting paths](phase-spec.md)
- [Shortest chains from a vertex whose level a phase keeps were chains before it](chain-of-chain-flip-phase.md)
- [The next phase's paths are strictly longer](lt-first-free-round-flip-phase.md)

## `O(√V)` phases

- [One round of the layered search bounds the deficit](card-le-card-pairs-add.md)
- [The deficit is at most $b / d$](mul-card-sub-le.md)
- [The phase loop stops when a step finds nothing](hopcroft-karp-aux-of-hk-step-none.md)
- [Fuel adds up in the phase loop](hopcroft-karp-aux-add.md)
- [Each phase lengthens the shortest augmenting paths](first-free-round-hopcroft-karp-aux.md)
- [Closing a deficit of $f$ in $f$ Hopcroft–Karp phases](card-le-hopcroft-karp-aux-of-le.md)
- [Hopcroft and Karp's bound on the number of phases](card-le-hopcroft-karp-aux-sqrt.md)
