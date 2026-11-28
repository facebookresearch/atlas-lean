# Envy-free cake divisions into connected pieces exist

Let $n$ agents have preferences given by nonatomic probability measures $v_1, \dots, v_n$ on $[0, 1]$. Then there exists a partition of $[0, 1]$ into $n$ intervals, made by $n - 1$ cuts, and an assignment of intervals to agents such that no agent values another agent's interval more than her own. The proof is existential: for $n \ge 3$ no finite protocol, one making finitely many marks on the cake in the Robertson–Webb style of cut and evaluation queries, finds such a division (Stromquist 2008, Theorem 1).

## Proof sketch

Parametrize divisions into $n$ intervals by the standard $(n-1)$-simplex of cut positions and triangulate it finely. Label each vertex of the triangulation with an agent owning it (according to a fully labelled assignment pattern) and the index of that agent's preferred interval at that division; an agent always prefers some nonempty interval to an empty one, since an empty interval has measure $0$ while some interval has measure at least $1/n$, so the labelling is a Sperner labelling. Sperner's lemma gives a fully labelled small simplex, and compactness and the continuity of interval values in the cut positions (the measures are nonatomic) yield in the limit a division in which each agent can be assigned a distinct preferred interval.

## Depends on

- [Cake cutting in the Robertson-Webb query model](../../cake-cutting-in-the-robertson-webb-query-model.md)
- [No finite protocol finds contiguous envy-free divisions for three or more agents](../envy-free-cake-cutting-query-complexity/no-finite-protocol-contiguous-envy-free.md)

## Sources

- W. Stromquist, "How to Cut a Cake Fairly", American Mathematical Monthly 87(8) (1980).
- W. Stromquist, "Envy-free cake divisions cannot be found by finite protocols", Electronic Journal of Combinatorics 15 (2008), #R11, Section 1 (existence for nonatomic measures with $n - 1$ cuts, citing the 1980 paper) and Theorem 1.
- F. E. Su, "Rental Harmony: Sperner's Lemma in Fair Division", American Mathematical Monthly 106(10) (1999).
