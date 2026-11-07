# Erdős Problem 992 has a negative answer

For a sequence of integers $(x_n)_{n \ge 0}$, a real
number $\alpha$ and a natural number $N$, let $D(N)$ be the supremum, over rationals $p, q$ with
$0 \le p \le q \le 1$, of $\lvert A(p, q) - (q - p) N \rvert$, where $A(p, q)$ is the number of
indices $n < N$ for which the fractional part $\{\alpha x_n\}$ lies in $[p, q]$. It is not true
that for every strictly increasing sequence of integers $x_0 < x_1 < \cdots$, for almost every
$\alpha \in [0, 1]$ and every $\varepsilon > 0$ there is a real constant $C$ with
$D(N) \le C \sqrt{N} (\log N)^{\varepsilon}$ for all sufficiently large $N$.

Berkes and Philipp construct an increasing integer sequence $(n_k)$ with
$\limsup_N \lvert \sum_{k \le N} \cos(2\pi n_k \alpha) \rvert / \sqrt{N \log N} = \infty$ for almost
every $\alpha$; by Koksma's inequality, $D(N)$ is then not $O(\sqrt{N} (\log N)^{\varepsilon})$ for
$\varepsilon < 1/2$.

## Sources

- C. Aistleitner, I. Berkes, R. Tichy, Lacunary sequences in analysis, probability and number theory, arXiv preprint (2023), arXiv:2301.05561 (reporting I. Berkes, W. Philipp, J. London Math. Soc. (2) 50 (1994), 454-464), https://arxiv.org/abs/2301.05561. Moved from `OpenConjectures/NumberTheory/ErdosSequenceDiscrepancy`.
