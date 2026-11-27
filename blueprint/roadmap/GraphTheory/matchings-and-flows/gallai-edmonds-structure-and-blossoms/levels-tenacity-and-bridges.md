# Even and odd levels, tenacity and bridges for minimum-length alternating paths

Fix a matching $M$ of a finite simple graph $G$. For a vertex $v$, $\mathrm{evenlevel}(v)$ (resp. $\mathrm{oddlevel}(v)$) is the length of a shortest even-length (resp. odd-length) $M$-alternating path, i.e. simple path whose edges alternate and whose first edge is not in $M$, from a vertex missed by $M$ to $v$, and is $\infty$ if no such path exists. Let $\mathrm{minlevel}(v)$ and $\mathrm{maxlevel}(v)$ be the smaller and larger of the two; $v$ is *outer* if $\mathrm{minlevel}(v)$ is even and *inner* if it is odd. The *tenacity* of $v$ is $\mathrm{tn}(v) = \mathrm{evenlevel}(v) + \mathrm{oddlevel}(v)$. An edge $uv$ is a *prop* if it is the last edge of some minlevel path of one of its endpoints, that is, of a shortest alternating path from a missed vertex to $v$ of length $\mathrm{minlevel}(v)$ ending with $uv$ (then $u$ is a *predecessor* of $v$, and $uv \in M$ exactly when $v$ is outer), or the same with $u$ and $v$ exchanged; it is a *bridge* otherwise; the tenacity of a bridge $uv$ is $\mathrm{evenlevel}(u) + \mathrm{evenlevel}(v) + 1$ if $uv \notin M$ and $\mathrm{oddlevel}(u) + \mathrm{oddlevel}(v) + 1$ if $uv \in M$. For a missed vertex $f$ one has $\mathrm{evenlevel}(f) = 0$, so $\mathrm{tn}(f)$ is the length of a shortest $M$-augmenting path ending at $f$, and the length of a shortest augmenting path equals $\min_f \mathrm{tn}(f)$.

## Depends on

- [Augmenting path](../berge-s-lemma/is-augmenting-walk.md)
- [Alternating forests, flowers and blossoms of a matching](alternating-forests-and-blossoms.md)

## Sources

- S. Micali, V. V. Vazirani, "An O(sqrt(|V|) |E|) algorithm for finding maximum matching in general graphs", FOCS (1980).
- V. V. Vazirani, "A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length", Mathematics of Operations Research 49 (2024) 2009-2047, doi:10.1287/moor.2020.0388.
- V. V. Vazirani, "A Proof of the MV Matching Algorithm", arXiv preprint (2020), arXiv:2012.03582.
- V. V. Vazirani, "A Simplification of the MV Matching Algorithm and its Proof", arXiv preprint (2012, revised 2013), arXiv:1210.4594.
