# Block-chain lemma for edit-distance neighbours

Let $s_1, \dots, s_n \in \Sigma^\ell$ be strings of a common length $\ell$, and call $s_i, s_j$ **neighbours** if their unit-cost edit distance is at most $d$. Split the positions $1, \dots, \ell$ into $b$ consecutive blocks of arbitrary lengths $w_1, \dots, w_b$ (so $\sum_i w_i = \ell$), the $i$-th block starting at $q_i = 1 + \sum_{j < i} w_j$. A **pattern** of length $k$ is a sequence $X = ((x_1, y_1), \dots, (x_k, y_k))$ of block indices $1 \le y_1 < \dots < y_k \le b$ and strings $x_t \in \Sigma^{w_{y_t}}$. The pattern **matches** a string $s$ with offsets $p = (p_1, \dots, p_k)$ if, for every $t$, the substring of $s$ of length $w_{y_t}$ starting at $q_{y_t} + p_t$ equals $x_t$.

**Theorem (block-chain lemma).** If $s_i$ and $s_j$ (of equal length $\ell$) are neighbours and $b > d$, there is a pattern $X$ of length $b - d$ that matches $s_i$ with all offsets $0$ and matches $s_j$ with offsets satisfying

$$-\lfloor d/2 \rfloor \le p_t \le \lfloor d/2 \rfloor, \qquad t = 1, \dots, b - d .$$

So every neighbour pair is found among pairs sharing such a pattern, one member at zero offset. Patterns are enumerated depth-first by extending one block at a time, grouping strings with equal block contents by radix sort and pruning when fewer than two strings remain or none matches at zero offset; candidate pairs are verified by computing a diagonal band of width $2d + 1$ of the edit-distance matrix in $O(d\ell)$ time. Duplicate reports are suppressed without memory by keeping only the **canonical** match, the occurrence $(y, p)$ that is lexicographically smallest (blocks first, then offsets); deciding whether a given match is canonical takes $O(d\ell)$ time.

**Affine gap costs.** If the cost is $f + g_o\gamma_o + g_e\gamma_e \le d$ with $f$ mismatches, $g_o$ gap openings and $g_e$ gap positions, equal lengths force equal numbers of gap positions $g$ in the two strings, so $g_e = 2g$ and $g_o \ge 2$ when $g > 0$; then $2g\gamma_e \le d - 2\gamma_o$ and the offsets can be restricted to $|p_t| \le \lfloor (d - 2\gamma_o)/(2\gamma_e) \rfloor$, shrinking the search when gaps cost more than substitutions.

## Expansion

Fix an optimal alignment of $s_i$ and $s_j$ with $M$ matches, $f$ mismatches and $g_i$, $g_j$ gap symbols in $s_i$ and $s_j$. Counting letters gives $\ell = M + f + g_j = M + f + g_i$, so $g_i = g_j$, and $g_i + g_j \le d$ gives $g_i = g_j \le \lfloor d/2 \rfloor$. Hence every aligned letter of $s_i$ sits within $\lfloor d/2 \rfloor$ positions of its partner in $s_j$. The alignment has at most $d$ edit operations, each touching at most one block of $s_i$, so at least $b - d$ blocks of $s_i$ contain no edit and are copied exactly, contiguously, into $s_j$ at a shift in $[-\lfloor d/2 \rfloor, \lfloor d/2 \rfloor]$. Those blocks, with their contents, form the required pattern.

## Sources

- K. Shimizu and K. Tsuda, "SlideSort: all pairs similarity search for short reads", Bioinformatics 27(4) (2011), 464–470, Section 2 (Theorem 1), Section 2.1–2.2 (pattern growth, canonical matches, Eq. (2)), Section 2.3 (gap costs, Eq. (3)), <https://doi.org/10.1093/bioinformatics/btq677> (PMC3035798).
