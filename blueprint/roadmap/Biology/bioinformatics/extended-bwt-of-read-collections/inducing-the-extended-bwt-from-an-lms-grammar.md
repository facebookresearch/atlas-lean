# Inducing the extended BWT from an LMS grammar

**Extended BWT.** For a collection $\mathcal T = \{T_1,\dots,T_m\}$ of strings (e.g. sequencing reads), let $T = T_1\#T_2\#\cdots T_m\#$. The *extended BWT* (eBWT) treats each $T_i\#$ as an independent circular string: it is the BWT of $T$ modified so that the $\mathsf{LF}$ step from the first symbol of $T_i$ goes to the sentinel at the end of $T_i$ (not of $T_{i-1}$).

**LMS grammar.** A symbol $T[i]$ is *L-type* if $T[i] > T[i+1]$, or $T[i] = T[i+1]$ with $T[i+1]$ L-type; otherwise *S-type* (the sentinel is S-type); it is *LMS-type* if S-type with $T[i-1]$ L-type. An *LMS substring* runs between consecutive LMS positions. The grammar compressor $\mathsf{LMSg}$ iterates: in round $i$ it cuts $T^i$ ($T^1 = T$) into LMS substrings, drops their first symbol, keeps the phrases that are long enough and contain a repeated symbol, sorts the phrases lexicographically (a phrase that is a proper prefix of another gets the larger rank), and replaces each phrase by a fresh nonterminal whose value is offset plus the phrase's lexicographic rank, producing $T^{i+1}$; phrases spanning two reads are split, so the grammar is *string independent* (every symbol of every $T^i$ expands within one read). Repeated length-two suffixes of right-hand sides become extra *SuffixPair* rules.

**Lemma (order consistency).** If two nonterminals $X < Y$ are produced in the same round, every suffix of $T$ whose prefix is compressed as $X$ is lexicographically smaller than every suffix whose prefix is compressed as $Y$. A suffix $S$ (of length $>1$) of a right-hand side that prefixes a suffix of $T^i$ determines that suffix's rank among suffixes with different prefixes.

**Lemma (induction step).** Let $B^i$ be the eBWT of $T^i$. (a) If $B^i[j]$ and $B^i[j']$ with $j<j'$ decompress one level to phrases $F$, $F'$ having suffix occurrences $S_j$, $S_{j'}$ of the same string $S$, then $S_j$ is lexicographically smaller than $S_{j'}$. (b) If $S$ ($|S| \ge 2$) occurs $x$ times in $T^{i-1}$, scanning the positions of $B^i$ whose phrases have $S$ as a suffix from left to right and collecting the symbol preceding each occurrence yields exactly a consecutive block $B^{i-1}[o..o+x-1]$.

Hence $\mathsf{infBWT}$ computes $B^h$ for the final compressed string and recovers $B^{h-1},\dots,B^1 = \mathrm{eBWT}(\mathcal T)$ level by level, sorting only distinct phrase suffixes and copying whole blocks; the work per input symbol drops as the collection becomes more repetitive, and runs of equal symbols in $B^i$ are processed together.

## Expansion

LMS-based parsing is the parsing step of SA-IS induced suffix sorting: the relative order of suffixes starting at LMS positions determines the order of all suffixes, and lexicographically ranked nonterminals preserve that order one level up (order consistency). Going down a level, each symbol of $B^i$ stands for a phrase; the suffixes of $T^{i-1}$ that start inside phrases are ordered first by the phrase suffix and then, among equal phrase suffixes, by the order already present in $B^i$, which is the block-copy lemma. String independence guarantees the circular, per-read semantics of the eBWT.

## Sources

- Diego Díaz-Domínguez and Gonzalo Navarro, "Efficient construction of the extended BWT from grammar-compressed DNA sequencing reads", arXiv:2102.03961 (2021), Section 2 (eBWT, LMS types, the $\mathsf{LMSg}$ grammar and its order-consistency and rank lemmas, string independence) and Section 3 (the $\mathsf{infBWT}$ algorithm and its induction lemmas), <https://doi.org/10.48550/arXiv.2102.03961>.
