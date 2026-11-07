# Guth–Maynard large values estimate

There is a function $o : \mathbb{R} \to \mathbb{R}$
with $o(T) \to 0$ as $T \to \infty$ such that the following holds. Let $(b_n)_{n \ge 0}$ be
complex numbers with $|b_n| \le 1$ for all $n$, let $N \ge 1$ and $R$ be natural numbers,
let $V > 0$ and $T > 1$ be real numbers, and let $t_0, \dots, t_{R-1}$ be points of $[0, T]$
with $|t_r - t_s| \ge 1$ whenever $r \ne s$. Suppose that, with $i$ the imaginary unit,

$$\left|\sum_{n=N}^{2N} b_n n^{i t_r}\right| \ge V$$

for every $r < R$. Then

$$R \le T^{o(T)} \left(N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4}\right).$$

The hypotheses $N \ge 1$, $V > 0$ and $T > 1$ are not stated in the paper; the inequality may
be false at $T = 1$.

## Sources

- L. Guth and J. Maynard, `New large value estimates for Dirichlet polynomials`, Annals of Math, 203 (2) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-2-LargeValueEstimates.lean Via leanprover/lean-eval@38361be, problem `annals_large_value_estimates`.
