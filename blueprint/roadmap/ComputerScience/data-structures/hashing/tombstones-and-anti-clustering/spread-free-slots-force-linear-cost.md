# Even perfectly spread free slots force $\Omega(x)$ scan length

Let $n$ circular slots contain $k \ge 1$ free slots, with $n = kx$. For a uniformly random start position $s$, let $D(s)$ be the number of occupied slots scanned from $s$ before reaching a free slot. Then $\mathbb{E}[D] = \frac{1}{2n}\sum_{i=1}^k g_i(g_i + 1)$, where $g_1, \dots, g_k$ are the numbers of occupied slots between consecutive free slots, and $\mathbb{E}[D] \ge \frac{x - 1}{2}$, with equality exactly when all gaps equal $x - 1$ (possible only when $x$ is an integer). For $x \ge 2$ the bound is at least $x/4$.

## Proof sketch

A start inside a gap of length $g$ at distance $t \in \{0,\dots,g\}$ from its end, counting the free slot itself as distance $0$, scans $t$ occupied slots, which sums to $g(g+1)/2$ per gap. The gaps sum to $n - k$, and by convexity of $g \mapsto g(g+1)$ the sum is minimized when all gaps equal $(n-k)/k = x - 1$, giving $\frac{k}{2n}(x-1)x = \frac{x-1}{2}$.

## Depends on

- [Linear probing with tombstones and periodic rebuilds](linear-probing-with-tombstones.md)

## Sources

- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250, Section 1 (the intuition that a table in which one slot in every $x$ is free should give $\Theta(x)$ insertions, against Knuth's $\Theta(x^2)$; the exact gap formula and its equality case above are elementary and are proved here, not in the paper).
