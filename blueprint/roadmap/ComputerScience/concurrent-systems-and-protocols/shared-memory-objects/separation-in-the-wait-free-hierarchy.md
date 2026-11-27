# Separation in the wait-free hierarchy

An object type $X$ solves $n$-process consensus if there is a wait-free consensus protocol for $n$ processes using objects of type $X$ and atomic read/write registers, each initialized to any state. The *consensus number* of $X$ is the largest such $n$, or $\infty$ if there is no largest.

**Theorem.** If $X$ has consensus number $n$ and $Y$ has consensus number $m < n$, then there is no wait-free implementation of $X$ by $Y$ in a system of more than $m$ processes.

**Proof.** Suppose $Y$ implements $X$ wait-free for $k > m$ processes, and let $r = \min(k, n)$, so that $m < r \le n$. Take a wait-free consensus protocol for $r$ processes that uses $X$ and registers, run it on $r$ of the $k$ processes, and replace each $X$ object by its implementation from $Y$, which remains wait-free when only $r$ processes take steps. Composition preserves wait-freedom and correctness, so this gives a wait-free $r$-process consensus protocol from $Y$ and registers, contradicting that the consensus number of $Y$ is $m < r$.

So objects of lower consensus number cannot implement objects of higher consensus number. For example, read/write registers have consensus number $1$; test-and-set, swap, fetch-and-add, queues and stacks have consensus number $2$; and compare-and-swap has infinite consensus number.

## Depends on

- [Consensus number](consensus-number.md)

## Background

- [Registers have consensus number one](registers-have-consensus-number-one.md)
- [FIFO queues have consensus number two](fifo-queues-have-consensus-number-two.md)
- [Compare-and-swap has infinite consensus number](compare-and-swap-has-infinite-consensus-number.md)

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991, <https://cs.brown.edu/~mph/Herlihy91/p124-herlihy.pdf>: Definition 1 (consensus number), Theorem 1 and its proof, and the classification of objects in Figure 1 and the following sections.
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, <https://cs.yale.edu/homes/aspnes/classes/4650/notes.pdf>, Chapter 19 (the wait-free hierarchy and classification by consensus number).
