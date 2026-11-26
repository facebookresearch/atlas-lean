# Hydrostructure characterization of circular safe walks

**Setting.** Let $G$ be a strongly connected directed (multi)graph with $n$ nodes and $m > n$ arcs that is not a single cycle (an assembly graph). A walk starts and ends in arcs. A *circular $k$-solution* is a set of at most $k$ closed walks that together cover every arc of $G$; a walk $W$ is *$k$-circular safe* if it is a subwalk of some walk in every circular $k$-solution (the 1-circular safe walks are the *omnitigs*).

**Hydrostructure.** For a walk $W$ with at least two arcs, define the restricted reachabilities
$$R^+(W) = \{x \in G : \exists\ \text{a walk from the start of } W \text{ to } x \text{ not containing } W\},$$
$$R^-(W) = \{x \in G : \exists\ \text{a walk from } x \text{ to the end of } W \text{ not containing } W\},$$
and partition $G$ (nodes and arcs) into
$$\mathsf{Sea} = R^+ \setminus R^-, \quad \mathsf{Cloud} = R^- \setminus R^+, \quad \mathsf{Vapor} = R^+ \cap R^-, \quad \mathsf{River} = G \setminus (R^+ \cup R^-).$$
For a walk, let $w_i$ be its first join arc and $w_j$ its last split arc; if $i < j$ the *non-trivial heart* $\mathrm{heart}(W)$ is the $w_i$–$w_j$ subwalk.

**Theorem (1-circular safety).** A non-trivial walk $W$ is 1-circular safe if and only if $\mathsf{Vapor}(\mathrm{heart}(W))$ is a path.

**Theorem ($k$-circular safety, $k \ge 2$).** A non-trivial walk $W$ is $k$-circular safe if and only if $\mathsf{Vapor}(\mathrm{heart}(W))$ is a path and $\mathsf{River}(\mathrm{heart}(W))$ is non-empty. In particular, all $k$-circular safety problems with $k \ge 2$ coincide.

**Linear models.** For safety with respect to $k$ open $s$–$t$ arc-covering walks, a trivial walk or non-trivial heart $W$ is safe iff it is a single arc, or the River cannot be covered by $k$ walks, or $s \notin R^-(W)$, or $t \notin R^+(W)$, or (for trivial walks) a further suffix–prefix covering condition on the trivial heart holds. All maximal linear $k$-safe walks can be reported in $O(mn + n\,f(m,n) + |\mathrm{out}|)$ time, where $f(m,n)$ is the cost of maintaining a minimum walk-cover size ($O(m)$ for $k=1$ or $k \ge m$, $O(m^2)$ otherwise); the same bounds hold for subset-covering ($F$-covering) variants.

## Depends on

- [Safe walk in a multigraph](../omnitigs-and-safe-walks-in-genome-assembly/is-safe.md)
- [Omnitig](../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md)

## Expansion

If the heart is avertible then $\mathsf{Vapor} = G$ and a closed walk can cover all arcs while avoiding the heart, so it is unsafe; if the Vapor is a path, every closed covering walk must leave the Sea and enter the Cloud, and the only connections from Sea back to Cloud pass through the heart, forcing it as a subwalk. With $k \ge 2$ walks, one walk can cover the Sea-related and another the Cloud-related strongly connected component unless a non-empty River must also be covered, which again forces traversing the heart. The hydrostructure gives a YES-certificate for safety, in contrast to earlier forbidden-path characterizations.

## Sources

- Massimo Cairo, Shahbaz Khan, Romeo Rizzi, Sebastian Schmidt, Alexandru I. Tomescu and Elia C. Zirondelli, "The Hydrostructure: a Universal Framework for Safe and Complete Algorithms for Genome Assembly", arXiv:2011.12635 (2020); definitions of restricted reachability and of the hydrostructure, theorems "1-Circular" and "$k$-Circular", the $k$-st safe trivial walks and non-trivial hearts theorem, and the improved linear runtime theorem, <https://doi.org/10.48550/arXiv.2011.12635>.
