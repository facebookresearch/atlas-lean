# Total positivity of hyper-Fibonacci Toeplitz matrices

Let $p, a, b$ be integers with $p \ge 1$, $a \ge 0$ and $b > 0$, put $\Delta = a^2 + pab - b^2$, and let $r \ge 1$. For $s \in \mathbb{N}$ let $T_s$ be the real $(r + 2) \times (r + 2)$ Toeplitz matrix with entry $W^{(r)}_{p,s+i-j}$ in row $i$ and column $j$. If $\Delta > 0$, then $T_{2n}$ is totally positive for all large $n$; if $\Delta < 0$, then $T_{2n+1}$ is totally positive for all large $n$.

## Idea

A Toeplitz matrix built from a sequence is totally positive when all its minors are positive, a strong form of log-concavity of the sequence. For the generalized hyper-Fibonacci numbers this holds eventually: for matrices of size $r + 2$ taken far enough along the sequence, along even or odd indices according to the sign of $\Delta = a^2 + pab - b^2$. For all large indices of either parity the minors of order at most $r + 1$ are positive; particular minors give the eventual positivity of Toeplitz determinants, and those of order one and two the eventual positivity and log-concavity of the numbers. The hyper $p$-Fibonacci numbers ($a = 0$, $b = 1$) and hyper $p$-Lucas numbers ($a = 2$, $b = p$) are special cases.

## Statements

- [Eventual total positivity of hyper-Fibonacci Toeplitz matrices](generalized-hyper-fibonacci-toeplitz-has.md)
- [Eventually positive bounded-order minors of hyper-Fibonacci Toeplitz matrices](generalized-hyper-fibonacci-toeplitz-pos.md): a variant for the minors of order at most $r + 1$, which are positive for all large $n$ of either parity
- [Eventual positivity of hyper-Fibonacci Toeplitz determinants](generalized-hyper-fibonacci-toeplitz-det.md): a weaker form: for each $m \ge 1$, the $m \times m$ Toeplitz determinants of $W^{(m-1)}$ are eventually positive (for $m \ge 2$, minors of order $r + 1$ of the previous statement, with $r = m - 1$)
- [Eventual positivity of lower-order hyper-Fibonacci Toeplitz determinants](generalized-hyper-fibonacci-toeplitz-det-2.md): a weaker form: the $m \times m$ Toeplitz determinants of $W^{(r)}$, $m \le r + 1$, are eventually positive, as leading minors of order at most $r + 1$
- [Eventual log-concavity of generalized hyper-Fibonacci numbers](generalized-hyper-fibonacci-eventually-l.md): a weaker form of the bounded-order minors statement: its minors of order one and two give eventual positivity and log-concavity, $W^{(r)}_{p,n} W^{(r)}_{p,n+2} \le (W^{(r)}_{p,n+1})^2$
- [Eventual log-concavity of hyper $p$-Fibonacci and hyper $p$-Lucas numbers](hyper-pfibonacci-hyper-plucas-eventually.md): the same for the hyper $p$-Fibonacci and hyper $p$-Lucas numbers
- [Total positivity of hyper $p$-Fibonacci Toeplitz matrices](hyper-pfibonacci-toeplitz-has-positive-m.md): special case: hyper $p$-Fibonacci numbers
- [Total positivity of hyper $p$-Lucas Toeplitz matrices](hyper-plucas-toeplitz-has-positive-minor.md): special case: hyper $p$-Lucas numbers
- [A binomial-sum formula for generalized hyper-Fibonacci numbers](generalized-hyper-fibonacci-sub-eq-sub.md): used in the proof of the eventual positivity of the Toeplitz determinants
- [Hankel determinants of generalized hyper-Fibonacci numbers](generalized-hyper-fibonacci-hankel-det.md): used in the proof of the main statement: reversing the columns of $T_s$ gives the Hankel matrix $H_{r,s-r-1}$
