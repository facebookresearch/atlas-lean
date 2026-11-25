# Elementary integrand

Let $F = (F_t)_{t \ge 0}$ be a filtration. An elementary integrand for $F$ consists of

1. a number $n \in \mathbb{N}$ of intervals;
2. times $0 \le t_0 \le t_1 \le \dots \le t_n$;
3. coefficients $\xi_0, \dots, \xi_{n-1}$, with $\xi_i$ measurable with respect to $F_{t_i}$;
4. a bound $C$ with $|\xi_i(\omega)| \le C$ for all $i$ and $\omega$.

It represents the [process](to-process.md) $\sum_i \xi_i \mathbf 1_{(t_i, t_{i+1}]}$. Equal consecutive times are
allowed (the corresponding interval is empty).

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 3.2.A.
