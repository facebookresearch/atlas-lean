# The pair map of the mod-prime family

Let $p$ be a natural number and fix two keys
$x, y \in \mathbb{Z}/p\mathbb{Z}$. The pair map at $x$ and $y$ sends an index $(a, b)$ of the
mod-prime family, that is, $a, b \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$, to the pair
$(ax + b, ay + b) \in (\mathbb{Z}/p\mathbb{Z})^2$ of inner hash values at $x$ and $y$.

This is the map used to count collisions in the universality argument for the mod-prime family.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 3rd ed.,
  MIT Press, 2009, Section 11.3.3, proof of Theorem 11.5.
