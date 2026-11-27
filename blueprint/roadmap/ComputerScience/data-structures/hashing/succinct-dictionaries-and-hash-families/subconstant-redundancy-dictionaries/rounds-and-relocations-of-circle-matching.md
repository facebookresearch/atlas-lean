# Rounds and relocations of multi-round circle matching

For the multi-round circle matching with $|A| \le n'$ active balls, every round matches at least one ball, so the process ends within $|A|$ rounds, and the matching is injective. The number of rounds $T$ satisfies $\mathbb{E}[T] = O(\log \max(|A|, 2))$ (Li, Liang, Yu and Zhou, Claim 3.3). Inserting or deleting one ball changes the bins of $O(T + 1)$ balls deterministically (Claim 3.4), and hence of $O(\log \max(|A|, 2))$ balls in expectation.

## Proof sketch

In each round a constant fraction of the remaining balls is followed clockwise by a remaining bin in expectation, because bins are at least as numerous as balls: with $a$ remaining balls and $b \ge a$ remaining bins, the expected number of matches is at least $a/2$, so $\mathbb{E}[|A_{i+1}| \mid A_i] \le |A_i|/2$, and by Markov's inequality the number of remaining balls drops by the factor $3/4$ with probability at least $1/3$ in each round (proof of Claim 3.3). Derived from the same halving, not stated in this form by the source: $\Pr[T \ge i] \le \min(1, |A| 2^{1-i})$, and summing over $i$ gives $\mathbb{E}[T] \le \lceil \log_2 \max(|A|, 1) \rceil + 2$. An update changes the outcome in each round only for the balls adjacent to the inserted or removed point, a constant number per round, and the remaining sets of the two runs differ in a single element in every round, so the updated run lasts at most one round longer (Claim 3.4).

## Depends on

- [Multi-round consistent-hashing matching on a circle](multi-round-circle-matching.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536 (Section 3.1: Claims 3.3 and 3.4).
- D. Karger, E. Lehman, T. Leighton, R. Panigrahy, M. Levine and D. Lewin, "Consistent Hashing and Random Trees: Distributed Caching Protocols for Relieving Hot Spots on the World Wide Web", Proceedings of the 29th ACM Symposium on Theory of Computing (STOC), pp. 654-663, 1997.
- A. Berger, W. Kuszmaul, A. Polak, J. Tidor and N. Wein, "Memoryless Worker-Task Assignment with Polylogarithmic Switching Cost", Proceedings of the 49th International Colloquium on Automata, Languages and Programming (ICALP), LIPIcs 229, pp. 19:1-19:19, 2022.
