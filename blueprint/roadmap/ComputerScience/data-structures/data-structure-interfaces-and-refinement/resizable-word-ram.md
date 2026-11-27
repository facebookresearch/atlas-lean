# Resizable Word RAM (virtual memory model)

The *resizable Word RAM* with word size $w$ is the Word RAM whose memory is an active prefix $[0, M)$ of $w$-bit words, where the *frontier* $M$ can change: besides reading and writing a word at an address $a < M$, a program may *allocate* a new word at the end of the prefix (increasing $M$ by one, with arbitrary initial contents) or *release* the last word (decreasing $M$ by one), each at unit cost and leaving the addresses and contents of all other words unchanged; growing or shrinking by $k$ words is $k$ such steps, and a variant zero-fills allocated words. A data structure occupying $[b, M)$ above a caller prefix $[0, b)$ has *resting space* $M - b$ after each completed operation and *peak space* the maximum of $M - b$ during an operation. Space bounds are measured in words of the active prefix rather than in a preallocated block, which allows space proportional to the current number of stored items.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- W. Kuszmaul, J. Liang and R. Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", Proceedings of the 2026 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 3760-3804, 2026; arXiv:2510.19175 (Section 5.1, the virtual memory model).
