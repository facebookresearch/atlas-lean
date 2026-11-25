# Satisfaction of quantifier-free Presburger normal forms in $\mathbb{N}$

Let $\psi$ be a quantifier-free Presburger normal form with $n$ bound variables and let $\vec{x} = (x_0, \dots, x_{n-1}) \in \mathbb{N}^n$. Terms are evaluated in the standard model $\mathbb{N}$, with $0$, $S(a) = a + 1$ and $a + b$ interpreted as usual and $x_i$ evaluated to the $i$-th coordinate of $\vec{x}$; write $t(\vec{x})$ for the value of a term $t$. Satisfaction of $\psi$ at $\vec{x}$ is defined by recursion on $\psi$:

- $\bot$ never holds;
- $s = t$ holds iff $s(\vec{x}) = t(\vec{x})$;
- $s < t$ holds iff $s(\vec{x}) < t(\vec{x})$;
- $t \equiv r \pmod{m+1}$ holds iff $t(\vec{x}) \bmod (m + 1) = r \bmod (m + 1)$;
- $\psi \to \chi$ holds iff $\chi$ holds whenever $\psi$ holds.

There are no free variables besides the bound ones, so the assignment of free variables is the empty map.
