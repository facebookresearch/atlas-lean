# Static predecessor problem on word keys

Given a set $K$ of $n$ distinct $w$-bit keys, a *predecessor structure* answers, for a query $q \in [2^w]$, the *inclusive predecessor* $\max\{x \in K : x \le q\}$, or reports that every key exceeds $q$. The *rank* of $q$ is $|\{x \in K : x \le q\}|$. On a word RAM with word size $w$, the goal is query time depending on $n$ and $w$ but not on the key values, using $O(n)$ words.

## Depends on

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
- E. D. Demaine, "6.851: Advanced Data Structures", lecture notes on integer data structures and fusion trees, Massachusetts Institute of Technology, 2012-2021.
