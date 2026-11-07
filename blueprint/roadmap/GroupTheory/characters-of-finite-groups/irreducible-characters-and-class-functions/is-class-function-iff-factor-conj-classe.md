# Class functions factor through conjugacy classes

Let $G$ be a group and $k$ a set,
and write $[x]$ for the conjugacy class of $x \in G$. A function $f : G \to k$ is a class
function if and only if there is a function $q$ from the set of conjugacy classes of $G$
to $k$ such that $f(x) = q([x])$ for all $x \in G$.

Proof: A class function is constant on each conjugacy class, so it descends to a function
on conjugacy classes. Conversely, if $f(x) = q([x])$ for all $x \in G$, then for all
$g, h \in G$ we have $f(h g h^{-1}) = q([h g h^{-1}]) = q([g]) = f(g)$, because
$h g h^{-1}$ and $g$ are conjugate.

## Sources

- `undergrad.yaml`, section "Representation theory of finite groups", entry "class function over a group"; J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2 (class functions as functions on conjugacy classes).
