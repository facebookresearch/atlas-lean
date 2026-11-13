# Specialized Stieltjes matrix

Let $R$ be an additive monoid with one and let
$a, b, \lambda, \mu \in R$. The specialized Stieltjes matrix is the tridiagonal Stieltjes
production matrix with $a_1 = a + \lambda$, $b_1 = b + \mu$ and the same $a$ and $b$: the infinite
matrix $S$ with rows and columns indexed by $\mathbb{N} = \{0, 1, 2, \dots\}$ whose entries are
$S_{i, i+1} = 1$ for every $i$, $S_{0,0} = a + \lambda$, $S_{1,0} = b + \mu$, $S_{i,i} = a$ and
$S_{i+1,i} = b$ for every $i \ge 1$, and $S_{i,j} = 0$ for all other $i, j$.

This specialization corresponds to the inverse Riordan pair with numerator
$1 - \lambda x - \mu x^2$ over $1 + a x + b x^2$.
