# Failure probability of a bounded number of uniform probes

Let $B$ be a subarray in which an $\varepsilon$ fraction of the slots is free, and let a key make $k$ independent uniform probes into $B$ while $B$ is unchanged. All $k$ probes hit occupied slots with probability exactly $(1 - \varepsilon)^k \le e^{-\varepsilon k}$, and the expected index of the first free probe, conditioned on success within $k$ probes, is at most $\varepsilon^{-1}$.

## Proof sketch

The probes are independent and each hits a free slot with probability $\varepsilon$, so the number of failures before success is geometric. The conditional expectation of a geometric variable truncated at $k$ is at most its unconditional mean $\varepsilon^{-1}$, and $1 - \varepsilon \le e^{-\varepsilon}$.

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
