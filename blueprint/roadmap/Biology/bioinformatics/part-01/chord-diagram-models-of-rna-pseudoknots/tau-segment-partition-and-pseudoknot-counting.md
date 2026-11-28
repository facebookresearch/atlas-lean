# τ-segment partition and pseudoknot counting

**Setting.** In a linear chord diagram $D$ (an RNA secondary structure), two chords $c,c'$ are *chord obstructed* if some other chord has an endpoint strictly between their left endpoints or strictly between their right endpoints. The *chord distance* is $d(c_1,c_2)=\max\{|\ell_1-\ell_2|,|r_1-r_2|\}$. For $\tau\ge0$, nested or crossed chords are *$\tau$-near* if $d(c_1,c_2)\le\tau$ and they are not chord obstructed; a *$\tau$-segment* is a maximal set of chords forming a $\tau$-near $k$-nesting or $\tau$-near $k$-crossing (consecutive chords $\tau$-near). The $\tau$-segments partition the chords. The *$\tau$-segment graph* $G_\tau$ has the $\tau$-segments as vertices, adjacent when they cross; for $\tau=0$ the construction reduces to the stem segments of the bpRNA method.

**Theorem (crossing is a segment property).** Let $S_1,S_2$ be $\tau$-segments of $D$. If some $c\in S_1$ crosses some $c'\in S_2$, then every chord of $S_1$ crosses every chord of $S_2$. The same holds for the ordinary segment partition.

**Definition (number of pseudoknots).** A structure is $\tau$-pseudoknotted if $G_\tau$ has an edge. For $\tau\ge1$ its number of pseudoknots is the minimum cardinality of a vertex cover of $G_\tau$; for $\tau=0$ it is the minimum cardinality among vertex covers of minimum weight, where each segment is weighted by its number of chords.

## Expansion

Because crossing is uniform between segments, the segment graph is a well-defined quotient of the chord intersection graph, and removing the chords of a vertex cover of $G_\tau$ leaves a crossing-free (planar) structure; minimal covers therefore count the helices that must be cut to remove all pseudoknots. The weighted ($\tau=0$) count can behave discontinuously, e.g. adding one base pair to a three-stem kissing structure lowers the count from 2 to 1, and lexicographic tie-breaking among optimal covers can change the pseudoknot type. Allowing $\tau$-near crossings to merge into one segment groups helices interrupted by small bulges, making the count robust; for large $\tau$ the partition stabilizes once $\tau$ exceeds the largest distance between non-obstructed neighbouring chords.

## Depends on

- [Genus equals vertex cover number for acyclic intersection graphs](genus-equals-vertex-cover-number-for-acyclic-intersection-graphs.md)

## Sources

- Rayan Ibrahim, Allison H. Moore, "Methods for Analyzing RNA Pseudoknots via Chord Diagrams and Intersection Graphs", arXiv:2512.19939: Section 2: Definitions 2.2, 2.3, 2.9, Theorem 2.8; Section 3: Theorem 3.1, Definition 3.2 and Examples 3.3–3.4. <https://doi.org/10.48550/arXiv.2512.19939>
