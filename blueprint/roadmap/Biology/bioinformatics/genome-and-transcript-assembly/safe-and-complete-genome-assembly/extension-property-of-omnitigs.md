# Extension property of omnitigs

**Setting.** Let $G$ be a strongly connected directed graph that is not a single closed path. For an arc $e$ write $t(e)$ and $h(e)$ for its tail and head. An arc $f$ is a *join* arc if $h(f)$ has in-degree at least two, and $G\setminus f$ is $G$ with the arc $f$ removed. Omnitigs are as in [Omnitig](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md).

**Theorem (Cairo–Rizzi–Tomescu–Zirondelli).** Let $fW$ be an omnitig of $G$, where $f$ is a join arc. Then $fWg$ is an omnitig if and only if $g$ is the only arc with $t(g)=h(W)$ such that there is a path from $h(g)$ to $h(f)$ in $G\setminus f$.

In particular, $fW$ has at most one extension to the right by an arc.

**Cost of one extension step.** After $O(m+n)$-time preprocessing of $G$ ($n$ nodes, $m$ arcs), the reachability data structure of Georgiadis et al. answers each query "does $h(g)$ reach $h(f)$ in $G\setminus f$?" in $O(1)$ worst-case time. Deciding the extension of $fW$ therefore takes one constant-time query per candidate arc $g$ leaving $h(W)$, that is $O(d^+(h(W)))$ time per extension step. Constant time per step holds only after the source's transformation of $G$ into a graph of constant degree with $O(m)$ nodes and arcs.

## Depends on

- [Omnitig](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md)

## Expansion

At least one such $g$ exists: a closed path through a sibling join arc $f'$ of $f$ must contain $W$ as a prefix, or it would yield a forbidden path for $fW$, and its arc after $W$ reaches $h(f)$ avoiding $f$. If a second arc $g'\ne g$ out of $h(W)$ reached $h(f)$ in $G\setminus f$, that path would be forbidden for $fWg$. Conversely, a forbidden path for $fWg$ must start with a sibling $g'$ of $g$, and an auxiliary lemma on such paths shows it can be chosen to end at $h(f)$ without using $f$.

## Sources

- Massimo Cairo, Romeo Rizzi, Alexandru I. Tomescu and Elia C. Zirondelli, "Genome assembly, from practice to theory: safe, complete and linear-time", arXiv:2002.10498 (2020); published in ICALP 2021, LIPIcs 198, paper 43, <https://doi.org/10.4230/LIPIcs.ICALP.2021.43>; numbering as in the arXiv version: Theorem 6 (Extension Property) with its proof in Section 5, Theorem 7 (constant-time reachability under one arc removal, from Georgiadis et al.), and Section 6.1 (constant-degree transformation).
