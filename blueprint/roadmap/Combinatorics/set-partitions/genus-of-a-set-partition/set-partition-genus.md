# Genus of a set partition

Let $\sigma$ be the cyclic permutation $i \mapsto i + 1 \pmod n$
of $\{0, \dots, n-1\}$. For a permutation $\tau$ of $\{0, \dots, n-1\}$, thought of as encoding the
set partition whose blocks are its cycles, let $|\alpha|$ be the number of cycles of $\tau$ and $c$
the number of cycles of $\sigma \circ \tau^{-1}$, fixed points counted as cycles in both. The genus
of $\tau$ is the integer part of $\frac{1}{2} \max(0,\ n + 1 - |\alpha| - c)$.

For $n \ge 1$ the number $n + 1 - |\alpha| - c$ is nonnegative and even, so the genus is the
number $g$ with $-2g = |\alpha| - 1 - n + c$; for $n = 0$ the genus is $0$.

## Sources

- Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*, Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4, equation (genus).
