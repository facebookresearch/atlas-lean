# Quantum Tanner checks commute

In a quantum Tanner code, every $X$-check commutes with every $Z$-check; hence the code is a well-defined CSS code. Moreover the code dimension satisfies

$$
k \ \ge\ n\Big(1 - 2\big(r_A r_B + (1 - r_A)(1 - r_B)\big)\Big),
$$

where $r_A, r_B$ are the rates of $C_A, C_B$; in particular $k \ge (1 - 2\rho)^2 n$ when $r_A = \rho$ and $r_B = 1 - \rho$.

## Proof sketch

A vertex of $V_0$ and a vertex of $V_1$ share either no square or exactly the $\Delta$ squares containing a common edge, which form a row (or a column) of both local views. The restriction of $c \in C_A \otimes C_B$ to that row lies in $C_B$ and that of $c' \in C_A^\perp \otimes C_B^\perp$ lies in $C_B^\perp$, so their overlap is even and $X^c$, $Z^{c'}$ commute. For the dimension, $|V_0| = |V_1| = |G|$ and each square has two vertices in each class, so $n = |V_0|\Delta^2/2$; subtracting the numbers of checks $|V_0| r_Ar_B\Delta^2$ and $|V_1|(1-r_A)(1-r_B)\Delta^2$ gives the bound.

## Depends on

- [Quantum Tanner codes](quantum-tanner-codes.md)

## Sources

- Anthony Leverrier, Gilles Zemor, "Quantum Tanner codes", FOCS (2022); arXiv:2202.13641.
