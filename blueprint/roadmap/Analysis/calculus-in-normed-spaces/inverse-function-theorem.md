# Inverse function theorem

Let $d\ge1$ and $k\ge1$, let $U\subseteq\mathbb R^d$ be open, and let $f:U\to\mathbb R^d$ be of class $C^k$. If $a\in U$ and the derivative $Df(a)$ is an invertible linear map, then there are open sets $V\subseteq U$ with $a\in V$ and $W\subseteq\mathbb R^d$ with $f(a)\in W$ such that $f$ restricts to a bijection $V\to W$ whose inverse $g:W\to V$ is of class $C^k$, with

$$Dg(f(x))=Df(x)^{-1}\qquad\text{for every }x\in V.$$

## Expansion

A proof page must establish local injectivity and the openness of $f(V)$ from the contraction mapping principle applied to $x\mapsto x+Df(a)^{-1}(y-f(x))$ on a small ball, using continuity of $Df$ to make $\|I-Df(a)^{-1}Df(x)\|\le\tfrac12$ there; differentiability of $g$ with the displayed derivative; and the $C^k$ regularity of $g$ by induction on $k$, from $Dg=(Df\circ g)^{-1}$ and the smoothness of matrix inversion on the invertible matrices.

## Sources

- W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, Chapter 9.
- M. Spivak, *Calculus on Manifolds*, W. A. Benjamin, 1965, Chapter 2.
