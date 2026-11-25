# Fundamental theorem of calculus for continuous integrands

Let $a<b$ and let $f:[a,b]\to\mathbb R$ be continuous. Then $F(x)=\int_a^xf(t)\,dt$ is differentiable on $[a,b]$, with one-sided derivatives at the endpoints, and $F'(x)=f(x)$ for every $x\in[a,b]$; in particular $F$ is continuously differentiable. Conversely, if $G:[a,b]\to\mathbb R$ is differentiable with $G'=f$ on $[a,b]$, then $\int_a^bf(t)\,dt=G(b)-G(a)$.

## Expansion

A proof page must establish $\lvert(F(x+h)-F(x))/h-f(x)\rvert\le\sup_{\lvert t-x\rvert\le\lvert h\rvert}\lvert f(t)-f(x)\rvert$ and conclude by continuity of $f$; and derive the converse from the first part and the mean value theorem applied to $G-F$.

## Sources

- W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, Chapter 6.
