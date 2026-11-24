# Constant rank theorem

Let $U\subseteq\mathbb R^d$ be open, let $k\ge1$, and let
$f:U\to\mathbb R^m$ be a $C^k$ map whose derivative $Df(y)$ has the same rank
$r$ for every $y$ in a neighbourhood of a point $x\in U$. Then there are open
neighbourhoods $V\ni x$ and $W\ni f(x)$ with $f(V)\subseteq W$, and $C^k$
diffeomorphisms $\varphi:V\to\varphi(V)\subseteq\mathbb R^d$ and
$\psi:W\to\psi(W)\subseteq\mathbb R^m$, such that

$$\psi\circ f\circ\varphi^{-1}(u_1,\ldots,u_d)=(u_1,\ldots,u_r,0,\ldots,0)
\qquad\text{on }\varphi(V).$$

In particular, near $x$ every fibre $f^{-1}(f(y))\cap V$ is a $C^k$
submanifold of dimension $d-r$. Rank $r$ at the single point $x$ is not
enough: the rank must be constant on a neighbourhood. The cases $r=0$ ($f$
locally constant) and $r=d$ (an immersion) are included.

## Expansion

A proof page must establish:

- Selection of a nonsingular $r\times r$ minor of $Df(x)$ and, after
  permuting coordinates, the local inverse of
  $(y_1,\ldots,y_d)\mapsto(f_1(y),\ldots,f_r(y),y_{r+1},\ldots,y_d)$ by the
  inverse function theorem.
- In the new coordinates, the vanishing of the derivatives of the remaining
  components with respect to $u_{r+1},\ldots,u_d$, which uses constancy of the
  rank on the neighbourhood.
- The construction of $\psi$, the fibre-dimension corollary, and the boundary
  cases $r=0$ and $r=\min(d,m)$.

It also uses:

- The inverse function theorem for $C^k$ maps between open subsets of
  $\mathbb R^d$.

## Sources

- John M. Lee, *Introduction to Smooth Manifolds*, 2nd edition, Springer (2013), Chapter 4, the rank theorem (smooth case; the same proof gives the $C^k$ case)
