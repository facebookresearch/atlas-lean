# Pair bijection of the mod-prime counting argument

Let $p$ be a prime and let $x \neq y$ be
elements of the field $\mathbb{Z}/p\mathbb{Z}$. The pair bijection for $x, y$ is the bijection
from the indices $(a, b)$, with $a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \neq 0$, to the ordered
pairs $(r, s)$ of elements of $\mathbb{Z}/p\mathbb{Z}$ with $r \neq s$ that sends $(a, b)$ to
the pair map value $(ax + b, ay + b)$. Its inverse solves the linear system $ax + b = r$,
$ay + b = s$: it sends $(r, s)$ to $(a, b)$ with $a = (r - s)/(x - y)$ and $b = r - ax$.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Section 11.3.3, proof of Theorem 11.5.
