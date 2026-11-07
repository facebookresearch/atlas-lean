# Growth bounds for Gibonacci and generalized Tribonacci sequences

Let $\varphi$ be the
golden ratio. For integers $x, y$ let $(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$
and $P_1 = y$, and for integers $a, b, c$ let $(Q_n)_{n \ge 0}$ be the generalized Tribonacci
sequence with $Q_0 = a$, $Q_1 = b$ and $Q_2 = c$. Then (i) for all integers $x, y$ and every
$n \ge 0$, $|P_n| \le (|x| + |y|)\,\varphi^n$; (ii) there are real constants $c_0 > 0$ and
$c_1 > 0$ such that for all integers $x, y$ with $(x, y) \ne (0, 0)$ and every $n \ge 0$ with
$c_1 (\log(|x| + |y|) + 1) \le n$, one has $c_0\,\varphi^{n+1} / (|x| + |y|) \le |P_n|$; and
(iii) for every real $\tau$ with $\tau^3 = \tau^2 + \tau + 1$, all integers $a, b, c$ and every
$n \ge 0$, $|Q_n| \le (|a| + |b| + |c|)\,\tau^n$.

The paper indexes both sequences from $1$, so its $n$-th terms are $P_{n-1}$ and $Q_{n-1}$ here.
It prints (ii) with the threshold "n large enough depending on $|x| + |y|$"; the logarithmic
threshold is the one the paper uses in its proof of Theorem 2.

## Sources

- Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 1 (`integers-2026-A122-lem-1`), with the threshold as used in the proof of Theorem 2.
