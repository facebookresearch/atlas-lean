# Cyclic compositions into odd parts and the Lucas numbers

Let $d_O(n)$ be the number of cyclic compositions of $n$ into odd parts and $d_\nu(n)$ the number of cyclic compositions of $n$ in which a part $a$ carries one of $a$ colors (in both cases any number of parts, the empty composition excluded). Let $L_k$ be the Lucas numbers ($L_0 = 2$, $L_1 = 1$, $L_{k+2} = L_{k+1} + L_k$) and $\varphi$ Euler's totient function. For every natural number $n \ge 1$, let $n_O = n / 2^{v_2(n)}$ be the greatest odd divisor of $n$. Then

$$2\, d_O(2n) - d_\nu(n) = d_O(n_O)$$

in $\mathbb{Z}$, and

$$d_O(n_O) = \frac{1}{n_O} \sum_{k \mid n_O} \varphi(k)\, L_{n_O / k}$$

in $\mathbb{Q}$, where $k$ runs over the positive divisors of $n_O$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 22.
