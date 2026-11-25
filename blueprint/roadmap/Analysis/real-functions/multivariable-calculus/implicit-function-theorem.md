# Implicit function theorem

Let $n,m\ge1$ and $k\ge1$, let $U\subseteq\mathbb R^n\times\mathbb R^m$ be open, and let $F:U\to\mathbb R^m$ be of class $C^k$. Write $D_xF$ and $D_yF$ for the partial derivatives in the two factors. If $(a,b)\in U$, $F(a,b)=0$ and $D_yF(a,b)$ is invertible, then there are open sets $A\subseteq\mathbb R^n$ with $a\in A$ and $B\subseteq\mathbb R^m$ with $b\in B$, with $A\times B\subseteq U$, and a unique map $g:A\to B$ such that for all $(x,y)\in A\times B$

$$F(x,y)=0\iff y=g(x).$$

Moreover $g$ is of class $C^k$, $g(a)=b$, and $Dg(x)=-D_yF(x,g(x))^{-1}D_xF(x,g(x))$ for every $x\in A$.

## Proof depends on

- [Inverse function theorem](../../calculus-in-normed-spaces/inverse-function-theorem.md)

## Expansion

A proof page must apply the [inverse function theorem](../../calculus-in-normed-spaces/inverse-function-theorem.md) to $\Phi(x,y)=(x,F(x,y))$, whose derivative at $(a,b)$ is invertible exactly when $D_yF(a,b)$ is, read $g$ off the second component of the local inverse, shrink the neighborhoods so that $g(A)\subseteq B$ and uniqueness holds, and obtain the derivative formula by differentiating $F(x,g(x))=0$.

## Sources

- W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, Chapter 9.
- M. Spivak, *Calculus on Manifolds*, W. A. Benjamin, 1965, Chapter 2.
