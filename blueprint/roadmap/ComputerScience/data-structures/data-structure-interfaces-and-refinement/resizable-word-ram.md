# Resizable Word RAM (virtual memory model)

The *resizable Word RAM* with word size $w$ is the Word RAM whose memory is an active prefix $[0, M)$ of $w$-bit words, where the *frontier* $M$ can change: besides reading and writing a word at an address $a < M$, a program may *grow* the prefix by $k$ words (either zero-filled or with arbitrary contents) or *shrink* it by $k$ words. A data structure occupying $[b, M)$ above a caller prefix $[0, b)$ has *resting space* $M - b$ after each completed operation and *peak space* the maximum of $M - b$ during an operation. Space bounds are measured in words of the active prefix rather than in a preallocated block, which allows space proportional to the current number of stored items.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- W. Kuszmaul, J. Liang and R. Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", Proceedings of the ACM-SIAM Symposium on Discrete Algorithms (SODA), 2026.
