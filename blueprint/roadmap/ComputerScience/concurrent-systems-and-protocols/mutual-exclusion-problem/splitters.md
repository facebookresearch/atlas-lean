# Splitters

A *splitter* is the following procedure over two atomic registers, $\mathit{race}$, which holds a process identifier and is initially $\bot$, and $\mathit{door}$, which is initially open. A process with identifier $\mathit{id}$ writes $\mathit{id}$ to $\mathit{race}$; if it then reads $\mathit{door} = \mathit{closed}$ it returns *right*; otherwise it writes $\mathit{closed}$ to $\mathit{door}$, and returns *stop* if it reads $\mathit{race} = \mathit{id}$ and *down* otherwise. Writing open to $\mathit{door}$ resets the splitter. The procedure has no loops, so each call takes a constant number of steps.

## Depends on

- [The asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235v6 (18 May 2026), <https://arxiv.org/abs/2001.04235v6>, Section 18.5.2 ("Fast mutual exclusion"), Algorithm 18.6 and the paragraphs after it, pp. 160–161.
