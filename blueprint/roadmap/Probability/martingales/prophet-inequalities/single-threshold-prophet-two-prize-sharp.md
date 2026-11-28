# The factor one half is sharp in the prophet inequality

Fix $0<\varepsilon\le 1$. The first prize is the constant $1$. The second prize equals $1/\varepsilon$ with probability $\varepsilon$ and zero otherwise. The expected maximum is $2-\varepsilon$. A deterministic policy makes its first accept-or-continue decision knowing only the first prize. After continuing it may observe the second prize and accept or reject it, receiving zero if it rejects. Every such policy has expected reward at most $1$.

Indeed, accepting the first prize pays $1$. Continuing yields at most the second prize, whose mean is $1$. The ratio of the best expected reward to the expected maximum is therefore $1/(2-\varepsilon)$, which tends to $1/2$ as $\varepsilon$ decreases to zero.

## Sources

- B. Lucier, *An economic view of prophet inequalities*, §2 (the two-chest example), <https://www.sigecom.org/exchanges/volume_16/1/LUCIER.pdf>.
