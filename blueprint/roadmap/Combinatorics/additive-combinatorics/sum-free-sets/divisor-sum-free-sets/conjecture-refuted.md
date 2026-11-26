# Erdős Problem 131 has a negative answer

It is not true that for every real
$\varepsilon > 0$ there is a natural number $N_0$ such that for every natural number $N \ge 1$ with
$N \ge N_0$ there is a set $S \subseteq \{1, \dots, N\}$ with $|S| > N^{1/2 - \varepsilon}$ that is
divisor-sum-free, meaning that no element $x \in S$ divides the sum of the elements of any nonempty
subset of $S \setminus \{x\}$.

Let $F(N)$ be the largest size of a divisor-sum-free subset of $\{1, \dots, N\}$. Every
divisor-sum-free set is non-averaging, that is, none of its elements is the average of other
elements of the set (an element equal to the average of $k$ others divides their sum), and Pham
and Zakharov (arXiv:2410.14624) prove that the largest non-averaging subset of $\{1, \dots, N\}$
has size $N^{1/4 + o(1)}$, so $F(N) \le N^{1/4 + o(1)}$; erdosproblems.com/131 records that this answers the question negatively. It also records a proof of $F(N) \le N^{1/5 + o(1)}$, which with Csaba's $F(N) \gg N^{1/5}$ gives the order of growth.

## Sources

- H. T. Pham and D. Zakharov, Sharp bound for the Erdős-Straus non-averaging set problem, arXiv:2410.14624 (2024), https://arxiv.org/abs/2410.14624.
- T. F. Bloom, Erdős Problem #131, https://www.erdosproblems.com/131.
