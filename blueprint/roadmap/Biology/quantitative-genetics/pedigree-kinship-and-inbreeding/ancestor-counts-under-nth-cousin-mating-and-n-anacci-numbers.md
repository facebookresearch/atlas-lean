# Ancestor counts under nth-cousin mating and n-anacci numbers

**Model.** In a large biparental population with equal sex ratio, every mating is between $n$th cousins ($n\ge0$; $n=0$ is sibling mating), so each mating pair shares one ancestral pair $g=n+1$ generations earlier. Let $A_t$ be the number of distinct genealogical ancestors of an individual $t$ generations back (Lachance's model). Then

$$A_t=\begin{cases}2^t,&0\le t\le g,\\ 2A_{t-1}-A_{t-g},&t\ge g+1,\end{cases}$$

since each new generation doubles the ancestors except that the pairs shared by cousin matings $g$ generations earlier are counted only once.

**Proposition 1 ($n$-anacci form).** For $g\ge2$ the sequence also satisfies $A_t=2^t$ for $0\le t\le g$ and

$$A_t=\sum_{i=1}^{g-1}A_{t-i}+2,\qquad t\ge g+1,$$

an inhomogeneous $n$-anacci recurrence with $n=g-1$.

**Corollary 2.** For second-cousin mating ($g=3$), $A_t=2f_{t+2}-2$ for $t\ge1$, where $f$ is the Fibonacci sequence ($f_0=0$, $f_1=1$).

**Proposition 3 (generating function).** $G_g(z)=\sum_{t\ge0}A_tz^t=\dfrac{1+z^g}{1-2z+z^g}=\dfrac{1+z^g}{z(1-z)}F_n(z)$, where $F_n(z)=z/(1-z-z^2-\dots-z^n)$ generates the $n$-anacci numbers.

**Proposition 4 (growth rates).** Let $c_n$ be the singularity of $F_n$ of smallest modulus. Then $c_{n+1}<c_n$ and $c_n\to\frac12$. Hence the asymptotic growth rate $r_g=\lim_tA_t/A_{t-1}=1/c_n$ of the number of ancestors increases with the degree of cousinship $n$ and tends to the outbred value $2$.

## Proof idea

Subtracting the recursion at $t$ and $t-1$ shows that $A_t-A_{t-1}=A_{t-1}-A_{t-g}$, and telescoping the original recursion over $g-1$ steps yields the $n$-anacci form, the constant $2$ coming from the initial segment $2^t$. Multiplying the recursion by $z^t$ and summing gives the rational generating function; since $1-2z+z^g=(1-z)(1-z-\dots-z^{g-1})$, the denominator factors through the $n$-anacci polynomial, so $A_t$ grows like $c_n^{-t}$. The smallest root $c_n$ of $1-z-\dots-z^n$ decreases in $n$ because each added term makes the polynomial smaller on $(0,1)$, and $c_n\to\frac12$ since $\sum_{k\ge1}z^k=1$ at $z=\frac12$. For $n=0$ the count stays at $2$ and for $n=1$ it grows linearly ($A_t=2t$), so only $n\ge2$ gives exponential growth below the outbred rate.

## Sources

- E. Heinrich Mora and N. A. Rosenberg, "An $n$th-cousin mating model and the $n$-anacci numbers", The Fibonacci Quarterly 64 (2026), 270–280, <https://doi.org/10.1080/00150517.2025.2581296>. Numbering as in the preprint arXiv:2506.16577v1, <https://arxiv.org/abs/2506.16577v1>: Propositions 1, 3, 4 and Corollary 2.
