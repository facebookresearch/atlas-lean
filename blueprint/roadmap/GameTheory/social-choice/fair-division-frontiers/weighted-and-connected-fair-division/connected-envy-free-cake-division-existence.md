# Envy-free cake divisions into connected pieces exist

Let $n$ agents have valuations on $[0, 1]$ that are nonatomic and such that each agent, offered any partition of $[0, 1]$ into $n$ intervals, weakly prefers some nonempty interval to every empty one (hungry agents). Then there exists a partition of $[0, 1]$ into $n$ intervals and an assignment of intervals to agents such that no agent prefers another agent's interval to her own. The proof is existential: no finite Robertson–Webb protocol computes such a division for $n \ge 3$.

## Proof sketch

Parametrize divisions into $n$ intervals by the standard $(n-1)$-simplex of cut positions and triangulate it finely. Label each vertex of the triangulation with an agent owning it (according to a fully labelled assignment pattern) and the index of that agent's preferred interval at that division; hungriness guarantees the labelling is a Sperner labelling. Sperner's lemma gives a fully labelled small simplex, and compactness and continuity yield in the limit a division in which each agent can be assigned a distinct preferred interval.

## Depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)
- [No finite protocol finds contiguous envy-free divisions for three or more agents](../envy-free-cake-cutting-query-complexity/no-finite-protocol-contiguous-envy-free.md)

## Sources

- W. Stromquist, "How to Cut a Cake Fairly", American Mathematical Monthly 87(8) (1980).
- F. E. Su, "Rental Harmony: Sperner's Lemma in Fair Division", American Mathematical Monthly 106(10) (1999).
