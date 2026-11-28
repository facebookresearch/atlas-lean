# Even perfectly spread free slots force $\Omega(x)$ scan length

Let $n$ circular slots contain $k \ge 1$ free slots, with $n = kx$. For a uniformly random start position $s$, let $D(s)$ be the number of occupied slots scanned from $s$ before reaching a free slot. Then $\mathbb{E}[D] = \frac{1}{2n}\sum_{i=1}^k g_i(g_i + 1)$, where $g_1, \dots, g_k$ are the numbers of occupied slots between consecutive free slots, and $\mathbb{E}[D] \ge \frac{x - 1}{2}$, with equality exactly when all gaps equal $x - 1$ (possible only when $x$ is an integer). This is Janson's block formula for the average cost $U$ of an unsuccessful linear-probing search started at a uniformly random cell of a table with $m$ cells: if the table has $N$ blocks, each a maximal run of occupied cells followed by its empty cell, of lengths $\ell_1, \dots, \ell_N$, then $U = \frac{1}{m}\sum_{j=1}^{N}\sum_{i=1}^{\ell_j} i$, and $U$ is smallest when all block lengths are as equal as possible, that is, all equal to $\lfloor m/N \rfloor$ or $\lceil m/N \rceil$ (Janson, Section 7, equation (7.1) and the remark after it). The statement above is this with $m = n$, $N = k$, $\ell_j = g_j + 1$ and $D = $ (number of probes) $- 1$.

## Proof sketch

A start inside a gap of length $g$ at distance $t \in \{0,\dots,g\}$ from its end, counting the free slot itself as distance $0$, scans $t$ occupied slots, which sums to $g(g+1)/2$ per gap. The gaps sum to $n - k$, and by convexity of $g \mapsto g(g+1)$ the sum is minimized when all gaps equal $(n-k)/k = x - 1$, giving $\frac{k}{2n}(x-1)x = \frac{x-1}{2}$; strict convexity makes this minimizer unique. In Janson's notation, $\mathbb{E}[D] = U - 1 = \frac{1}{m}\sum_j\big(\frac{\ell_j(\ell_j+1)}{2} - \ell_j\big) = \frac{1}{2n}\sum_j g_j(g_j+1)$. For $x \ge 2$, $\frac{x-1}{2} \ge \frac{x}{4}$, so the scan length is $\Omega(x)$.

## Depends on

- [Linear probing with tombstones and periodic rebuilds](linear-probing-with-tombstones.md)

## Sources

- Svante Janson, "Asymptotic Distribution for the Cost of Linear Probing Hashing", Random Structures & Algorithms 19(3–4) (2001), 438–471, Section 7, equation (7.1) and the remark after it.
- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250, Section 1 (motivation only: the intuition that a table in which one slot in every $x$ is free should give $\Theta(x)$ insertions, against Knuth's $\Theta(x^2)$).
