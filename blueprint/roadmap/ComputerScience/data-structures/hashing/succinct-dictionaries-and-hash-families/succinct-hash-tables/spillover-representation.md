# Spillover representation of a bounded integer

Let $X \ge 1$ and let $r \ge 1$ be an integer. Set $M = 0$ if $X \le r$ and $M = \lfloor \log_2(X / r) \rfloor$ otherwise, and $K = \lceil X / 2^M \rceil$. The *spillover representation* of $x \in [X]$ is the pair $(\lfloor x / 2^M \rfloor, x \bmod 2^M) \in [K] \times [2^M]$: an $M$-bit word stored in memory together with a *spill* value in the small universe $[K]$ that is passed to metadata. Decoding is $x = k 2^M + m$.

For $X > r$ this is the encoding in the proof of Lemma 3 of Pătraşcu, which assumes $r \le |X|$; the case $X \le r$ (no memory bits, spill universe $[X]$) is the extension noted with Lemma 3.8 of Li, Liang, Yu and Zhou.

## Sources

- M. Pătraşcu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 305-313, 2008 (Section 2, Lemma 3).
- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536 (Section 3.2 and Lemma 3.8).
