# Hybrid pseudoalignment and key k-mers of a colored de Bruijn graph

Let $D = (R_1, \dots, R_n)$ be reference sequences (with their reverse complements), and let the node-centric de Bruijn graph of order $k$ have the distinct $k$-mers of $D$ as nodes and an edge $u \to v$ when $u[2..k] = v[1..k-1]$. The *color set* $S(x) \subseteq \{1, \dots, n\}$ of a $k$-mer $x$ is the set of indices $i$ with $x$ (or its reverse complement) in $R_i$.

**Pseudoalignment rules.** For a query $Q$ and threshold $\tau \in [0,1]$:
- *threshold method*: report $R_i$ if at least a fraction $\tau$ of all $k$-mers of $Q$ occur in $R_i$;
- *intersection method*: report $\bigcap \{S(x) : x \text{ a } k\text{-mer of } Q,\ S(x) \ne \emptyset\}$, i.e. require every $k$-mer found in the index to occur in $R_i$, ignoring $k$-mers absent from all references;
- *hybrid method*: with $K(Q)$ the list of $k$-mers of $Q$ found in at least one reference, report $R_i$ if and only if at least $\tau\,|K(Q)|$ of them occur in $R_i$.

The hybrid method with $\tau = 1$ is exactly the intersection method, and the hybrid method computed over all $k$-mers of $Q$ instead of $K(Q)$ is the threshold method.

**Key $k$-mers.** Call a node $v$ a *key $k$-mer* if (1) some out-neighbour of $v$ is the first $k$-mer of a reference sequence, (2) $v$ is the last $k$-mer of a reference sequence, (3) some out-neighbour of $v$ has indegree at least $2$, or (4) $v$ has outdegree at least $2$. Then:

**Lemma.** If $v$ is not a key $k$-mer, then $v$ has exactly one out-neighbour $u$ and $S(v) = S(u)$. Consequently the color set of every node equals that of the first key $k$-mer reached by the unique forward walk from it, and only key $k$-mers need explicit color sets.

## Expansion

Ignoring $k$-mers that occur in no reference makes the rule robust to sequencing errors, adapters and gaps in the database. The fraction $\tau$ still tolerates true variation between the query and the reference. For the lemma: not (2) means $v$ ends no reference, so its outdegree is at least $1$, and not (4) caps it at $1$; let $u$ be the unique out-neighbour. Every reference through $v$ continues to $u$, since none ends at $v$, so $S(v) \subseteq S(u)$. Conversely $u$ has indegree $1$ by not (3), and no reference starts at $u$ by not (1), so every reference through $u$ arrives from $v$ and $S(u) \subseteq S(v)$. The forward walk from a non-key node passes only through outdegree-one nodes and must stop at a key node, because reference ends are key. So the key $k$-mers, essentially the ends of colored unitigs, suffice. Storing additional color-set pointers on every $d$-th node of these walks bounds lookups by $d$ steps.

## Sources

- J. N. Alanko, J. Vuohtoniemi, T. Mäklin, S. J. Puglisi, "Themisto: a scalable colored k-mer index for sensitive pseudoalignment against hundreds of thousands of bacterial genomes", *Bioinformatics* (2023), Section 2 (notation), Section 3.1 (threshold and intersection methods), Section 3.2 (hybrid method) and Section 3.3 (key $k$-mers and Lemma 1 with proof), <https://doi.org/10.1093/bioinformatics/btad233> (PMC10311346).
