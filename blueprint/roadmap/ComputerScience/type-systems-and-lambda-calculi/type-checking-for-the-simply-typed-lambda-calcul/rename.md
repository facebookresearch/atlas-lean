# Renaming of raw terms

Given a map $\rho : \mathbb{N} \to \mathbb{N}$ on de Bruijn indices,
renaming a raw term by $\rho$ replaces each variable $n$ by $\rho(n)$, renames both parts of an
application by $\rho$, and renames the body of a lambda abstraction, keeping its parameter type,
by the lifted map $\rho'$ given by $\rho'(0) = 0$ and $\rho'(n + 1) = \rho(n) + 1$.
