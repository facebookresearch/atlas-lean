# Zaslavsky's formulas for the anti-Fibonacci numbers

Let $A_1 = 1$, $B_1 = 2$,
$C_1 = 3$, and for $n \ge 1$ let $A_{n+1} < B_{n+1}$ be the two smallest positive integers not
among $A_1, B_1, C_1, \ldots, A_n, B_n, C_n$ and $C_{n+1} = A_{n+1} + B_{n+1}$. Let
$\mathrm{PD}[0], \mathrm{PD}[1], \ldots$ be the letters of the period-doubling word, the fixed
point of $1 \mapsto 10$, $0 \mapsto 11$ starting with $1$. Then for every $k \ge 0$,
$C_{2k+1} = 10k + 3$, $C_{2k+2} = 10k + 8 + \mathrm{PD}[k]$, $A_{2k+1} = 5k + 1$,
$B_{2k+1} = 5k + 2$, $A_{2k+2} = 5k + 3 + \mathrm{PD}[k]$, and $B_{2k+2} = 5(k + 1)$.

In the source's notation the anti-Fibonacci numbers are $X_n = C_n$ and the
non-anti-Fibonacci numbers are $Y_{2n-1} = A_n$ and $Y_{2n} = B_n$, so the formulas read
$X_{2k+1} = 10k + 3$, $X_{2k+2} = 10k + 8 + \mathrm{PD}[k]$, $Y_{4k+1} = 5k + 1$,
$Y_{4k+2} = 5k + 2$, $Y_{4k+3} = 5k + 3 + \mathrm{PD}[k]$ and $Y_{4k+4} = 5(k + 1)$ (the
source's $Y_{4k} = 5k$ for $k \ge 1$). The source's prose writes the period-doubling word
over letters $a, b$ with $a = 0$, but its Walnut code and its values $X_2 = 9$ and $Y_3 = 4$
need $\mathrm{PD}[0] = 1$.

## Sources

- Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8, Theorem 11 (`jis-2025-25.3.8-thm-11`), due to Zaslavsky.
