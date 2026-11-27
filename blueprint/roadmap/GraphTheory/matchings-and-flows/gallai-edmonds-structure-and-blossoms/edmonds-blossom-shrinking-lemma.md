# Edmonds' blossom shrinking lemma

Let $M$ be a matching of a finite simple graph $G = (V, E)$ and let $B$ be a blossom of $M$ that is part of a flower. Then $M$ is a maximum matching of $G$ if and only if $M / B$ is a maximum matching of $G / B$. Moreover, every $(M / B)$-augmenting path in $G / B$ can be turned in $O(|V| + |E|)$ time into an $M$-augmenting path of $G$: a path avoiding $\beta$ is kept, and a path through $\beta$ is expanded by replacing $\beta$ with the even-length $M$-alternating path around $B$ from the vertex $x \in B$ that is the endpoint in $G$ of the path's non-matching edge at $\beta$ to the base $b$ (empty when $x = b$); the path's matching edge at $\beta$, if any, is the stem edge at $b$.

## Proof sketch

Replacing $M$ by its symmetric difference with the stem keeps $|M|$, keeps $B$ a blossom and makes its base $b$ missed, so assume the stem is trivial. An $(M/B)$-augmenting path avoiding $\beta$ is augmenting in $G$; one through $\beta$ enters $B$ at some vertex $x$, and exactly one of the two arcs of $B$ from $x$ to $b$ has even length and alternates correctly, giving an augmenting path of $G$. Conversely, if $M$ is not maximum, Berge's lemma gives an $M$-augmenting path $P$; if $P$ meets $B$, one endpoint of $P$ is not $b$, and the initial segment of $P$ from that endpoint up to its first vertex of $B$ becomes an augmenting path of $G/B$ ending at the missed vertex $\beta$.

## Depends on

- [Alternating forests, flowers and blossoms of a matching](alternating-forests-and-blossoms.md)
- [Augmenting path](../berge-s-lemma/is-augmenting-walk.md)

## Proof depends on

- [Berge's lemma for matching subgraphs](../berge-s-lemma/berge-general.md)
- [Augmenting along a path (Hopcroft–Karp, Lemma 1)](../berge-s-lemma/symm-diff-is-matching.md)

## Sources

- J. Edmonds, "Paths, trees, and flowers", Canadian Journal of Mathematics 17 (1965).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
