# Approximate counting by pairwise independent hashing

Let $S$ be a finite set with $|S| \le 2^n$. For each level $j \in \{0, \dots, n\}$ let $(h_s)_{s}$ be a pairwise independent family of hash functions into a set $Y_j$ of size $2^j$, with a target $y_j \in Y_j$. Answer level $j$ *yes* if more than $r$ of $2r$ independent uniformly random hash functions $h$ at that level satisfy $h(x) = y_j$ for some $x \in S$. The *Stockmeyer estimate* is $0$ if level $0$ answers no and otherwise $2^{k}$ for the largest level $k \le n$ answering yes.

1. If every level with $|S|/2^j \ge 8$ answers yes, every level with $|S|/2^j \le 1/8$ answers no, and level $0$ answers yes exactly when $S \neq \emptyset$, then the estimate $E$ satisfies $|S|/16 \le E \le 8|S|$.
2. The majority answers satisfy these conditions except with probability at most $(n+1)(8/9)^r$; hence with $r = 12(n+1)$ the estimate is within a factor $16$ below and $8$ above $|S|$ with probability at least $3/4$.
3. (Relative error) Applying the estimator to the Cartesian power $S^{k}$ with $k = 7p$ copies for an integer $p \ge 1$ and taking the integer $k$-th root of $16E$ gives an estimate $\hat s$ with $|S| \le \hat s \le (1 + 1/p)|S|$, except with probability at most $2^{-t}$ when each level uses $2r$ trials with $r = 6(n + 1 + t)$, where $|S|^k \le 2^n$.

## Proof sketch

At level $j$ with mean cell size $\lambda = |S|/2^j$, pairwise independence and inclusion-exclusion (or Chebyshev) show that $S$ meets the target cell with probability at least $7/8$ when $\lambda \ge 8$ and at most $\lambda \le 1/8$ when $\lambda \le 1/8$. A majority of $2r$ independent trials errs with probability at most $(8/9)^r$ (majority amplification at advantage $3/8$), and a union bound over the $n+1$ levels gives item 2; item 1 is bookkeeping on the largest yes level. For item 3, a constant factor $128$ on $|S|^k$ becomes $128^{1/k} \le 1 + 1/p$ after the $k$-th root, since $(1+1/p)^p \ge 2$.

## Depends on

- [Pairwise-independent hashing by affine maps over GF(2)](../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Proof depends on

- [Pairwise-independent hashing by affine maps over GF(2)](../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- L. J. Stockmeyer, "The Complexity of Approximate Counting", Proceedings of the 15th Annual ACM Symposium on Theory of Computing (STOC), 1983.
