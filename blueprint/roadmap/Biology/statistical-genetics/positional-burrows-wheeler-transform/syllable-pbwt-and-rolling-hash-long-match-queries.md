# Syllable PBWT and rolling-hash long-match queries

**Setting.** A haplotype panel consists of $M$ aligned binary sequences of $N$ sites. For a query $z$ and threshold $L$, an $L$-long match with panel haplotype $x$ is a maximal interval $[b,e)$ with $x[b,e) = z[b,e)$ and $e - b \ge L$. The long-match query problem asks for all such matches.

**Syllabic panel.** Fix a syllable length $B$ and cut every haplotype into $n = \lceil N/B \rceil$ blocks; read block $k$ of haplotype $i$ as a $B$-bit integer $\bar x_i[k]$. At each syllable $k$ let $r_k$ be the sorted list of distinct values $\{\bar x_i[k]\}$, and replace $\bar x_i[k]$ by its rank $x_i[k] \in \{0, \dots, |r_k|-1\}$ (coordinate compression, so $x_i[k] < M$).

**Proposition (prefix arrays by counting sort).** Let $a_k$ order the haplotypes by their reversed syllabic prefixes $x_i[0,k)$. Then $a_{k+1}$ is obtained from $a_k$ by a stable sort on the key $x_i[k]$, so all $n$ positional prefix arrays are built in $O(Mn)$ time and memory by counting sort.

**Proposition (rolling-hash interval matching).** With large primes $\mathrm{BASE}, \mathrm{MOD}$ define prefix hashes $h(x_i, k) = \sum_{0 \le j < k} (x_i[j] + 1)\,\mathrm{BASE}^j \bmod \mathrm{MOD}$. Then the hash of the positional substring $x_i[j,k)$ is $h(x_i,k) - h(x_i,j) \bmod \mathrm{MOD}$, so equality of two aligned haplotypes on any syllable interval is tested in $O(1)$ after $O(Mn)$ preprocessing (up to hash collisions), replacing the divergence arrays of the binary PBWT.

**Lemma (match persistence).** Any $L$-site match covers at least $l = \lfloor (L - B + 1)/B \rfloor$ full syllables. Once a panel haplotype matching the query on the last $l$ syllables is found immediately above the query's virtual position in $a_k$, it stays immediately above the query until that match ends. Hence each potential long match can be reported exactly once.

## Expansion

The PBWT sorts haplotypes by reversed prefixes so that sequences sharing the longest ongoing match with a given sequence form a contiguous block around it. Replacing sites by syllables keeps this property, because two haplotypes agree on a syllabic prefix exactly when they agree on the underlying binary prefix. Linkage disequilibrium makes few syllable values distinct at each position, so the dictionaries $r_k$ are small and the syllabic panel needs far less memory than the binary panel with its auxiliary arrays. A query is inserted virtually by binary search in $a_k$, using the hashes for $O(\log n)$ lexicographic comparisons; ongoing matches are found by scanning outward from the query's position until the last-$l$-syllable hash comparison fails, and their ends are located by binary search on hashes. Match boundaries are refined to single-site resolution with bit operations on the raw syllable values. On UK Biobank and 1000 Genomes data this cut memory by more than a factor of 100 compared with the previous fastest long-match query method.

## Sources

- V. Wang, A. Naseri, S. Zhang, D. Zhi, "Syllable-PBWT for space-efficient haplotype long-match query", Bioinformatics (2023) btac734, Sections 2.2–2.4 (syllabic panel, positional prefix arrays, polynomial prefix hash, Lemma 1), <https://doi.org/10.1093/bioinformatics/btac734>, PMCID PMC9805553.
