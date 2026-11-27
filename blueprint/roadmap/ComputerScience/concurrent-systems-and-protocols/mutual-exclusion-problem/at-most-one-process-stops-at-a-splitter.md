# At most one process stops at a splitter

In any execution of [splitter](splitters.md) calls in which each process calls the splitter at most once, the following holds for each time $t$ at which $\mathit{door}$ is set to open, and for the start of the execution, where it is open initially: among the processes that read open from $\mathit{door}$ after $t$ and before the next write of closed to $\mathit{door}$, at most one later returns *stop*. The count is per cohort of door reads, not per interval of returns: a process that read open before a reset, returning *stop* after it, belongs to the earlier cohort, so two processes can return *stop* between the same two resets.

## Depends on

- [Splitters](splitters.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235v6 (18 May 2026), <https://arxiv.org/abs/2001.04235v6>, Lemma 18.5.3 and its proof, pp. 161–162.
