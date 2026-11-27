# Mapability function and the unambiguous read-extension criterion

**Definitions.** Let $G$ be a genome (a string, or a set of strings) and $s$ a sequence. For an integer $m \ge 0$ let $S_m(s) = \{s' : |s'| = |s|,\ \mathrm{mismatch}(s, s') \le m\}$ be the set of same-length sequences within Hamming distance $m$ of $s$. The *mapability* of $s$ in $G$ is

$$M(s, G, m) = \sum_{s' \in S_m(s)} \#\{\text{occurrences of } s' \text{ in } G\}, \qquad M(s, G) := M(s, G, 0),$$

so $M(s, G)$ counts exact occurrences. For $k \ge 1$, the *$k$-mapability map* of $s$ lists the mapability of each $k$-mer of $s$ in order:

$$MM(s, G, k, m) = \bigl[M(s_{[0,k)}, G, m),\ M(s_{[1,k+1)}, G, m),\ \dots\bigr],$$

where $s_{[a,b)}$ is the substring from position $a$ to $b - 1$ (0-based).

**Lemma 1 (monotonicity in the sequence).** If $s'$ is a substring of $s$, then $M(s, G) \le M(s', G)$. When $s'$ occurs exactly once inside $s$, equality holds iff every occurrence of $s'$ in $G$ lies inside an occurrence of $s$.

**Lemma 2 (monotonicity in the mismatch tolerance).** If $m > m'$, then $M(s, G, m) \ge M(s, G, m')$.

**Unambiguous extension criterion.** In overlap-based assembly of a target genome $G$, let a contig end in a sequence $s$ that overlaps a read $r$ (so $s$ is a prefix of $r$), with $s$ occurring exactly once in $r$. By Lemma 1, extending the contig with $r$ is guaranteed unambiguous iff

$$M(s, G) = M(r, G),$$

i.e. $s$ never occurs in $G$ outside $r$. When $M(s, G) > M(r, G)$, the surplus $M(s, G) - M(r, G)$ counts genomic copies of $s$ that do not continue as $r$. In a whole-genome experiment these copies generate *misleading reads*: reads that share the overlap but extend into a different sequence. Their expected number scales with this surplus and with the read-count distribution over a region of that length (Poisson for uniform sampling).

## Expansion

Every occurrence of $s$ contains an occurrence of $s'$ at the fixed offset where $s'$ sits inside $s$, so occurrences of $s$ inject into occurrences of $s'$. Equality means the injection is onto, i.e. no copy of $s'$ lies outside a copy of $s$. Lemma 2 holds because $S_{m'}(s) \subseteq S_m(s)$. These facts let a simulator predict assembly behaviour without generating reads genome-wide. Precomputing mapability maps of a target region for a range of $k$ (read lengths) and mismatch levels gives, for any overlap, the number of competing genomic copies. A simulated assembler then either extends correctly, follows an over-represented misleading extension, or stops at the longest extension common to all supporting reads. A paired-end read whose mate maps uniquely in the reference ($M(r', G) = 1$) anchors the extension. The resulting reconstruction rates for large novel insertions guide the choice of long-, medium- and short-read coverages that minimizes cost at a target accuracy.

## Sources

- J. Du, R. D. Bjornson, Z. D. Zhang, Y. Kong, M. Snyder, M. B. Gerstein, "Integrating sequencing technologies in personal genomics: optimal low cost reconstruction of structural variants", PLoS Computational Biology 5 (2009) e1000432, Materials and Methods, Definitions 1–2 and Lemmas 1–2, sections "The mapability data" and "Simulation of same/similar/misleading-reads in de novo reconstruction", <https://doi.org/10.1371/journal.pcbi.1000432> (PMC2700963).
