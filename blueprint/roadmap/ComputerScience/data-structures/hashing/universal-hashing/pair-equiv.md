# Pair bijection of the CLRS counting argument

Let $p$ be a prime and let $x \neq y$ be
elements of the field $\mathbb{Z}/p\mathbb{Z}$. The pair bijection for $x, y$ is the bijection
from the indices $(a, b)$, with $a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \neq 0$, to the ordered
pairs $(r, s)$ of elements of $\mathbb{Z}/p\mathbb{Z}$ with $r \neq s$ that sends $(a, b)$ to
the pair map value $(ax + b, ay + b)$. Its inverse solves the linear system $ax + b = r$,
$ay + b = s$: it sends $(r, s)$ to $(a, b)$ with $a = (r - s)/(x - y)$ and $b = r - ax$.
