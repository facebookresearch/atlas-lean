# The randomized marking algorithm and the harmonic lower bound for paging

Consider paging with a fast memory of $k$ pages, equivalently the uniform $k$-server problem on $n > k$ vertices, against an oblivious adversary. Let $H_k = 1 + \frac12 + \dots + \frac1k$.

1. **Marking algorithm.** Each requested page is marked; when $k + 1$ pages are marked, all marks except the one on the page just requested are erased. On a request to a page not in fast memory, a page chosen uniformly at random among the unmarked pages in fast memory is evicted. This algorithm is $2H_k$-competitive: on every request sequence its expected cost is at most $2H_k$ times the optimal offline cost, up to an additive constant.
2. **Lower bound.** No randomized online paging algorithm is $c$-competitive with $c < H_k$, for any $1 \le k \le n - 1$.

The lower bound is proved by an adversary that restricts requests to $k + 1$ pages and tracks, for each page, the probability that the algorithm does not hold it. In each phase it forces expected cost at least $H_k$, while the optimal offline cost is $1$. Raghavan gives a different proof from a generalization of Yao's minimax principle.

## Sources

- A. Fiat, R. M. Karp, M. Luby, L. A. McGeoch, D. D. Sleator and N. E. Young, "Competitive paging algorithms", *Journal of Algorithms* 12(4):685–699, 1991; arXiv:cs/0205038, <https://arxiv.org/abs/cs/0205038>: Section 3 (the marking algorithm) and Theorem 1, Section 5, Theorem 4 and Corollary 5.
