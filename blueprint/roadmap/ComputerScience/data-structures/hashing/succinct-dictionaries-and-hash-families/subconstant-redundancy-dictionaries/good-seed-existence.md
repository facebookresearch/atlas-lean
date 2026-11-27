# Existence of good seed assignments for the dictionary tree

In the polynomial-universe regime, for all sufficiently large $n$ and every key set of size $n$ or $n - 1$, the probability, over independently drawn node seeds, that some node of the multi-level dictionary tree overflows or underflows (receives more than $\overline{n}_\ell$ or fewer than $\underline{n}_\ell$ keys) or produces an identifier collision is less than $1$; in particular a good seed assignment exists, and the tree can be built bottom-up from any such assignment. Given good seeds at the strict ancestors of a level-$\ell$ node $u$ (so that $u$ receives between $\underline{n}_\ell$ and $\overline{n}_\ell$ keys), a fresh seed for $u$ fails, by letting a child of $u$ overflow or underflow or by an identifier collision at $u$, with probability at most $3 / n_\ell^2$ (Li, Liang, Yu and Zhou, Sections 5.4 and 5.5), and the top-level router fails with probability at most $1/(4n^2)$. The source does not state this existence claim separately; it is what makes their rehashing procedure (Algorithm 4) terminate.

## Proof sketch

Each child load is a sum of indicators that are highly independent under the child router, whose round function comes from Thorup's double tabulation family, so the limited-independence Chernoff bound gives failure probability at most $1/(4m^2) \le 1/n_\ell^2$ when $u$ receives $m \ge n_\ell / 2$ keys; the per-child identifier permutation is $2$-wise independent, so a collision among the at most $\overline{n}_\ell$ keys of $u$ has probability at most $\overline{n}_\ell^2 / 2^{I_\ell} \le 2/n_\ell^2$. A union bound over all nodes does not work, since there are $n / n_k$ leaves; instead draw the seeds top-down: conditioned on all ancestors being good, each node is good with probability at least $1 - 3/n_\ell^2 > 0$, so all nodes are good simultaneously with positive probability.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Proof depends on

- [Bucket-load concentration for Feistel routing](feistel-routing-concentration.md)
- [Thorup's high independence of double tabulation](../word-ram-hash-families/high-independence-of-double-tabulation.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 90-99, 2013; arXiv:1311.3121.
