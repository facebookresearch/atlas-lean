# Generalized hyper-Fibonacci numbers

Let $p, a, b$ be integers and let $(W_{p,n})$ be the generalized Fibonacci sequence with $W_{p,0} = a$, $W_{p,1} = b$ and $W_{p,n+2} = pW_{p,n+1} + W_{p,n}$. The generalized hyper-Fibonacci numbers are defined by $W^{(0)}_{p,n} = W_{p,n}$ and, for $r \ge 1$, $W^{(r)}_{p,n} = \sum_{k=0}^{n} p^{n-k} W^{(r-1)}_{p,k}$.

## Idea

The generalized Fibonacci sequence includes the Fibonacci numbers ($p = 1$, $a = 0$, $b = 1$), the Pell numbers ($p = 2$, $a = 0$, $b = 1$) and the corresponding Lucas numbers, as instances of Lucas sequences. Hyper-Fibonacci numbers iterate a weighted partial-sum operation on it, as hyper-Fibonacci numbers in the classical sense iterate partial sums of the Fibonacci numbers. They satisfy a two-index recurrence and have closed binomial-sum formulas and explicit Hankel determinants. The same source studies the total positivity of the Toeplitz matrices built from them; for $r \ge 1$, $p \ge 1$, $a \ge 0$ and $b > 0$, their eventual log-concavity is the case of minors of order two.

## Statements

- [Generalized hyper-Fibonacci numbers](generalized-hyper-fibonacci.md)
- [Generalized $p$-Fibonacci sequence](generalized-pfibonacci.md): the generalized $p$-Fibonacci sequence
- [$p$-Fibonacci numbers as a Lucas sequence](generalized-pfibonacci-zero-one.md): the $p$-Fibonacci numbers as a Lucas sequence
- [$p$-Lucas numbers as a companion Lucas sequence](generalized-pfibonacci-two-p.md): the $p$-Lucas numbers as a companion Lucas sequence
- [Initial values of generalized hyper-Fibonacci numbers](generalized-hyper-fibonacci-zero-one.md): initial values
- [Recurrence for generalized hyper-Fibonacci numbers](generalized-hyper-fibonacci-succ-succ.md): the recurrence
