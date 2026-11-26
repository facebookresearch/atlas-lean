# Space savings of filter-augmented compressed static functions

**Setting.** A static key–value table has $N$ keys and $n$ distinct values $v_0,v_1,\dots$ with frequencies $f_0\ge f_1\ge\cdots$; the majority fraction is $\alpha=f_0/N$. Highly skewed tables are typical of $k$-mer count tables, where most $k$-mers share one count. A *compressed static function* (CSF) stores the map without storing keys: values are Huffman-encoded with lengths $l_i$, and the code bits are recovered by solving a random linear system over $\mathrm{GF}(2)$ with overhead factor $\delta$ ($\delta\approx1.089$ with three hashes, $\approx1.024$ with four). Its cost is

$$
C_{\mathrm{CSF}}=\delta\sum_i f_il_i+D_V+D_e,
$$

where $D_V$ stores the vocabulary and $D_e=n\lceil\log_2\max_il_i\rceil$ the canonical Huffman code lengths. A *filtered* CSF first inserts the $N-f_0$ minority keys into an approximate membership filter with false-positive rate $\epsilon$ and $b(\epsilon)$ bits per key; keys rejected by the filter are answered $v_0$, and the CSF stores only minority keys plus the $f_0'$ majority keys that are false positives ($\mathbb E f_0'=\epsilon f_0$).

**Theorem (lower bound on savings).** For any filter with cost function $b(\epsilon)$,

$$
\frac{C_{\mathrm{CSF}}-\mathbb E[C_{\mathrm{FSF}}]}{N}\ \ge\ \alpha\delta(1-\epsilon)-(1-\alpha)\,b(\epsilon)-\frac nN .
$$

**Decision rule (AutoCSF).** Let $\epsilon^*=\arg\max_\epsilon\big[\alpha\delta(1-\epsilon)-(1-\alpha)b(\epsilon)\big]$. Build the filtered CSF with false-positive rate $\epsilon^*$ if $\alpha\delta(1-\epsilon^*)-(1-\alpha)b(\epsilon^*)-n/N>0$, and a plain CSF otherwise. Since typically $n=o(N)$, the last term is negligible.

*Example (Bloom filter).* With $b(\epsilon)=C_{\mathrm{BF}}\log_2(1/\epsilon)$ and a CSF cost of $C_{\mathrm{CSF}}$ bits per key, the earlier BCSF analysis gives the optimum $\epsilon^*=\frac{C_{\mathrm{BF}}}{C_{\mathrm{CSF}}}\frac{1-\alpha}{\alpha}\log_2e$ and the criterion that a filter helps iff $\alpha>\frac{C_{\mathrm{BF}}\log_2e}{C_{\mathrm{CSF}}+C_{\mathrm{BF}}\log_2e}$.

## Expansion

Removing majority keys can only shrink the optimal Huffman cost: the code built for frequencies $(f_0',f_1,\dots)$ is at least as good on those frequencies as the old code, so $\sum f_il_i'\le f_0'l_0+\sum_{i\ge1}f_il_i$ and the encoded payload drops by at least $\delta l_0(f_0-f_0')\ge\delta(f_0-f_0')$. Lowering one frequency deepens the Huffman tree by at most one level, so the codebook grows by at most $n$ bits. The filter costs $b(\epsilon)(N-f_0)$. Taking expectations over the filter's hashing gives the bound. Because it only involves $\alpha$, $\delta$ and $b$, the rule applies to any membership structure (Bloom, XOR, binary fuse filters), replacing the empirical entropy-fit cost model of the BCSF heuristic with a provable guarantee: whenever the rule chooses a filter, the expected space is strictly smaller.

## Sources

- David Torres Ramos, Vihan Lakshman, Chen Luo, Todd Treangen, "AutoCSF: Provably Space-Efficient Indexing of Skewed Key-Value Workloads via Filter-Augmented Compressed Static Functions", arXiv:2603.24882 (2026), Section 3 (BCSF criterion), Section 4: Algorithm 1, Theorems 4.1–4.2 (lower bound) and Theorem 4.3, <https://doi.org/10.48550/arXiv.2603.24882>.
