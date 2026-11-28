# Fragment filtering for approximate circular string matching

**Setting.** Let $x = x[0..m-1]$ be a pattern and $t$ a text of length $n > m$ over an alphabet $\Sigma$ of size $\sigma$. The $i$-th rotation of $x$ is $x^i = x[i..m-1]\,x[0..i-1]$, $0 \le i < m$. Write $u \equiv_k v$ when two strings of equal length differ in at most $k$ positions (Hamming distance at most $k$).

- *Exact circular string matching:* find all factors $u$ of $t$ with $u = x^i$ for some $i$.
- *Approximate circular string matching with $k$ mismatches* ($k < m$): find all factors $u$ of $t$ with $u \equiv_k x^i$ for some $i$.

**Fact 1.** Every rotation of $x$ is a factor of $x' = x[0..m-1]\,x[0..m-2]$ (length $2m-1$), and every length-$m$ factor of $x'$ is a rotation of $x$.

**Lemma 1 (exact case).** Partition $x'$ into $4$ consecutive fragments of lengths $\lfloor (2m-1)/4 \rfloor$ and $\lceil (2m-1)/4 \rceil$. Then at least one fragment is entirely contained in any length-$m$ factor of $x'$, hence in every rotation of $x$.

**Lemma 2 (pigeonhole).** If $x$ and $y = y_0 y_1 \cdots y_k$ have length $n$, the $y_i$ are $k+1$ non-empty blocks and $x \equiv_k y$, then some block $y_i$ starting at position $j$ of $y$ occurs exactly at position $j$ of $x$.

**Lemma 3 ($k$-mismatch case).** Partition $x'$ into the $2k+4$ evenly spread fragments $x'[c_i..c_{i+1}-1]$, $0 \le i < 2k+4$, with cut points $c_i = \lfloor i(2m-1)/(2k+4) \rfloor$ (so every fragment has length $\lfloor (2m-1)/(2k+4) \rfloor$ or $\lceil (2m-1)/(2k+4) \rceil$). Then at least $k+1$ of the fragments are contained in any length-$m$ factor of $x'$. This evenly spread form is the page's own corrected form of the source's Lemma 3, proved in the Expansion; no cited source states it. The source prints "If we partition $x' = x[0..m-1]x[0..m-2]$ in $2k+4$ fragments of length $\lfloor(2m-1)/(2k+4)\rfloor$ and $\lceil(2m-1)/(2k+4)\rceil$, at least $k+1$ of the $2k+4$ fragments are factors of any factor of length $m$ of $x'$", for any arrangement of the two lengths, which is false (for $m = 8$, $k = 3$, see the Expansion).

**Theorem (average-case complexity).** Search the $2k+4$ fragments of Lemma 3 in $t$ with an Aho–Corasick automaton and verify each fragment hit by extending it left and right with at most $k$ mismatches (constant-time longest-common-extension queries on a suffix array, or direct character comparison). For a uniformly random text this algorithm runs in average time

$$O\!\left(\left(1 + \frac{k\,m}{\sigma^{(2m-1)/(2k+4)}}\right) n\right)$$

and space $O(n)$ (Theorem 2); the variant without suffix-array preprocessing uses space $O(m)$ (Theorem 3). In particular, if $k = O(m/\log_\sigma m)$ the average time is $O(n)$ (Corollaries 1 and 2); for $k = 0$ the exact algorithm runs in average time $O(n)$ (Theorem 1).

## Expansion

Lemma 1: a window of $x'$ that contains no whole fragment lies inside one fragment without covering it, or inside two consecutive fragments without the first position of the first and the last position of the second, so its length is at most $2\lceil (2m-1)/4 \rceil - 2$; since $2\lceil (2m-1)/4 \rceil - 1 \le m$, every window of length $m$ contains a whole fragment. Lemma 3: for a window $x'[s..s+m-1]$ let $a$ be the first index with $c_a \ge s$, so $c_{a-1} \le s-1$ (or $a = 0$ when $s = 0$). Because $\lfloor u+v \rfloor - \lfloor u \rfloor \le \lceil v \rceil$, any $k+2$ consecutive fragments span $c_{j+k+2} - c_j \le \lceil (k+2)(2m-1)/(2k+4) \rceil = m$ positions, so $c_{a+k+1} \le s+m-1$ and the fragments $a, \dots, a+k$ lie inside the window; $a+k+1 \le 2k+4$ because $c_{k+3} \ge m-1 \ge s$. The even spread matters: the source states Lemma 3 for any arrangement of the two fragment lengths, arguing from $\ell_f \le (2m-1)/(2k+4)$, which fails for every longer fragment, and the statement is then false. For $m = 8$, $k = 3$, the ten fragments of lengths $2,2,2,2,2,1,1,1,1,1$ leave only three whole fragments in $x'[1..8]$. Combined with Lemma 2, any occurrence of a rotation with at most $k$ mismatches contains some fragment occurring exactly, at the right offset. The verification cost is driven by the expected number of spurious fragment hits, $O(k\,n\,\sigma^{-(2m-1)/(2k+4)})$, each checked in $O(m)$ time; this is bounded by $c\,n$ when the fragment length exceeds about $\log_\sigma m$, which holds for $k = O(m/\log_\sigma m)$. Because each edit operation touches at most one fragment, the same filter is valid under edit distance, with an $O(m^2)$ dynamic-programming verification around each hit.

## Sources

- C. Barton, C. S. Iliopoulos, S. P. Pissis, "Fast algorithms for approximate circular string matching", Algorithms for Molecular Biology 9 (2014) 9, Fact 1, Lemmas 1–3, Theorems 1–3 and Corollaries 1–2, <https://doi.org/10.1186/1748-7188-9-9>, PMCID PMC4234210.
