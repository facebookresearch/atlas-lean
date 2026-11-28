# FM-index construction of the string graph of sequencing reads

**Setting.** Let $R$ be a set of $n$ reads of length $m$ over a constant alphabet $\Sigma$, each terminated by a sentinel. Read $r_i$ *overlaps* $r_j$ if a nonempty suffix $\beta$ of $r_i$ is a prefix of $r_j$: $r_i = \alpha\beta$, $r_j = \beta\gamma$. Here $\beta$ is the overlap, $\gamma$ the right extension of $r_i$, and $\alpha$ the left extension of $r_j$. The **overlap graph** has an arc $(r_i,r_j)$ for each overlap, and a path $\langle r_1,\dots,r_k\rangle$ spells the assembly $r_1\,rx_{1,2}\cdots rx_{k-1,k}$. An arc $(r_1,r_3)$ is **transitive** (redundant) if some arc $(r_2,r_3)$ has an extension that is a suffix of the extension of $(r_1,r_3)$, so that $r_1 \to r_2 \to r_3$ spells the same string. The **string graph** is the overlap graph with all transitive arcs removed. It loses no assembly information and keeps repeats shorter than a read resolved, which a $k$-mer de Bruijn graph does not.

**Arc-sets.** For strings $\alpha$, $\beta \ne \varepsilon$ and a set $X$ of reads having prefix $\beta$, the arc-set $ARC(\alpha,\alpha\beta,X)$ is the set of pairs $(r_1,r_2)$ with $\alpha\beta$ a suffix of $r_1$, $\beta$ a prefix of $r_2$ and $r_2 \in X$. All suffixes of an overlap are potential overlaps.

**Lemma (transitivity test).** An arc $(r_1,r_2)$ with overlap $\beta$ is transitive iff $r_1 = \gamma\alpha\beta$ and $r_2 = \beta\delta\eta$ for nonempty $\alpha,\gamma,\delta,\eta$, and some input read $r_3 = \alpha\beta\delta$ makes $(r_3,r_2)$ an irreducible arc of a nonempty correct arc-set $ARC(\alpha,\alpha\beta\delta,X)$ for every $X \ni r_2$.

**Theorem (correctness and complexity).** Given only the FM-index (Burrows–Wheeler transform) of $R$, without access to the reads themselves, the FSG algorithm outputs exactly the arcs of the string graph. It processes arc-sets in clusters of common extension suffixes, and each irreducible arc with extension $\alpha$ is produced in exactly the $|\alpha| + 1$ clusters $C(\alpha), C(\alpha[2:]),\dots,C(\varepsilon)$ and output once. The overlap phase takes $O(nm)$ time, one constant-time step per potential overlap, of which there are $O(nm)$ suffixes. The reduction phase handles $O(nm^2)$ arc-sets. With union and difference of destination sets costing $d(n)$, the total time is $O(nm\,d(n))$; with $n$-bit vectors the paper bounds it by $O(nm(n+m))$.

## Expansion

Backward search in the FM-index enumerates, for each candidate overlap $\beta$, the interval of reads beginning with $\beta$ (via the sentinel-terminated suffixes) and the interval of suffixes ending reads with $\beta$, in time proportional to $|\beta|$ and incrementally in $\beta$. Extending the left extension one character at a time ($\alpha \to c\alpha$) moves through the clusters. A destination read already reached by a shorter-extension irreducible arc (a terminal arc-set) is removed from longer-extension arc-sets, which is the transitivity test above. What remains are exactly the irreducible arcs.

## Sources

- Paola Bonizzoni, Gianluca Della Vedova, Yuri Pirola, Marco Previtali and Raffaella Rizzi, "FSG: Fast String Graph Construction for De Novo Assembly of Reads Data", arXiv:1604.03587 (2016), Section 2 (definitions), Section 3 (Proposition 1, Definitions 1–3, Lemmas 2–3, Theorem 7), Section 4 (complexity), <https://doi.org/10.48550/arXiv.1604.03587>.
