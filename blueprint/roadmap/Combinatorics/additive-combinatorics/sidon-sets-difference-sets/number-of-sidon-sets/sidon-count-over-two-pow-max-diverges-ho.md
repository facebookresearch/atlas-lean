# Erdős Problem 861, first question: positive answer

Let $A(N)$ be the number of Sidon
subsets of $\{1, \dots, N\}$, including the empty set and the singletons, and let $f(N)$ be the
largest size of a Sidon subset of $\{1, \dots, N\}$. Then $A(N) / 2^{f(N)} \to \infty$ as
$N \to \infty$.

Saxton and Thomason proved $A(N) \ge 2^{(1.16 + o(1)) \sqrt{N}}$ (Theorem 2.11), and
$f(N) \sim \sqrt{N}$, so $A(N) / 2^{f(N)} \ge 2^{(0.16 + o(1)) \sqrt{N}} \to \infty$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #861, https://www.erdosproblems.com/861 (status SOLVED); resolution: D. Saxton and A. Thomason, Hypergraph containers, Invent. Math. (2015), 925-992, arXiv:1204.6595 (lower bound); Y. Kohayakawa, S. J. Lee, V. Rödl and W. Samotij, The number of Sidon sets and the maximum size of Sidon sets contained in a sparse random set of integers, Random Structures Algorithms (2015), 1-25 (upper bound), Saxton-Thomason Theorem 2.11: there are between 2^{(1.16 + o(1)) √n} and 2^{(55 + o(1)) √n} Sidon subsets of [n], the lower bound answering negatively whether there are only 2^{(1 + o(1)) √n}; erdosproblems.com/861: f(N) ∼ N^{1/2}, both questions are settled, the first positively and the second negatively, and 2^{1.16 f(N)} ≤ A(N) ≤ 2^{6.442 f(N)} for large N, https://arxiv.org/abs/1204.6595.
