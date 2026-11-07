# Recurrence for ascending $k$-Naples parking functions

Let $I_{n,k}$ be the number of
weakly increasing $k$-Naples parking functions of length $n$, let $U_{n,k}$ be the number of
those whose first entry is $1$, and let $C_k$ be the $k$-th Catalan number. For all natural
numbers $n$ and $k$ with $1 \le k \le n - 1$,

$$I_{n,k} = I_{n,k-1} + C_k \sum_{i=0}^{n-k} I_{i,k-1} \, U_{n-k-i,k}$$

and

$$U_{n,k} = U_{n,k-1} + C_k \sum_{i=0}^{n-k} U_{i,k-1} \, U_{n-k-i,k}.$$

## Sources

- J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez, *Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024), Article A44, Theorem 3.
