# Turnstile streams, support size and linear sketches of a frequency vector

A *turnstile stream* over the universe $[n] = \{1, \dots, n\}$ is a sequence of updates $(i_t, \Delta_t) \in [n] \times \{-M, \dots, M\}$ acting on a vector $x \in \mathbb{Z}^n$, initially zero, by $x_{i_t} \leftarrow x_{i_t} + \Delta_t$; the stream length and $M$ are at most $\mathrm{poly}(n)$. The stream is *insertion-only* if every $\Delta_t = +1$ (then $x$ is the frequency vector of the stream of elements $i_1, i_2, \dots$), and *strict turnstile* if $x \ge 0$ coordinatewise after every update. Write

$$
\|x\|_0 = |\{i : x_i \ne 0\}|, \qquad \|x\|_p^p = \sum_{i=1}^{n} |x_i|^p \quad (p > 0),
$$

so that in the insertion-only case $\|x\|_0 = F_0$ is the number of distinct elements and $\|x\|_p^p = F_p$ is the $p$-th frequency moment. A *linear sketch* is a streaming algorithm whose memory, apart from its random seed, is $Ax$ (possibly reduced modulo a prime) for a random matrix $A$ with few rows; linear sketches handle deletions and merge by addition.

## Depends on

- [Frequency of an element in a stream](../../frequency-moments-of-data-streams/freq.md)
- [Frequency moment of a stream](../../frequency-moments-of-data-streams/freq-moment.md)
- [Randomized streaming algorithm with $s$ bits of memory](../../frequency-moments-of-data-streams/streaming-algorithm.md)

## Sources

- Hossein Jowhari, Mert Sağlam, Gábor Tardos, "Tight Bounds for Lp Samplers, Finding Duplicates in Streams, and Related Problems", PODS (2011), arXiv:1012.4889.
- Daniel M. Kane, Jelani Nelson, David P. Woodruff, "An Optimal Algorithm for the Distinct Elements Problem", PODS (2010).
