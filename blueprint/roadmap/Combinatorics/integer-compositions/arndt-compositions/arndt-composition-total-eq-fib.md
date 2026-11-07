# Arndt compositions are counted by Fibonacci numbers

Let $a(n, m)$ be the number of Arndt
compositions of $n$ with $m$ parts, let $a(n) = \sum_{m=0}^{n} a(n, m)$ be the number of all
Arndt compositions of $n$, and let $F_n$ be the $n$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$).
Then, in $\mathbb{Z}[[x]]$,

$$\Big(\sum_{n \ge 0} a(n) x^n\Big)(1 - x - x^2) = 1 - x^2,$$

and $a(n) = F_n$ for every $n \ge 1$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Corollary 2 (`integers-2024-A35-cor-2`).
