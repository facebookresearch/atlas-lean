# Unit quaternions double cover the rotation group

This node covers the double cover of $SO(3)$ by the unit quaternions. For a quaternion $q$ with $|q| = 1$, the map
$R(q) : v \mapsto q v \bar q$ on the pure-imaginary quaternions $\cong \mathbb{R}^3$ is a rotation, and $q \mapsto R(q)$ is a surjective group
homomorphism from the unit quaternions onto $SO(3)$ with kernel $\{1, -1\}$. Explicitly, every rotation by angle $\theta$ about a unit axis $n$
is $R(q)$ for $q = \cos(\theta/2) + \sin(\theta/2)\,n$ and for $-q$ only.

## Expansion

A good expansion proves that $R(q)$ is an orthogonal map of determinant one and that $q \mapsto R(q)$ is a homomorphism with kernel
$\{\pm1\}$, then proves surjectivity by Euler's theorem that every element of $SO(3)$ is a rotation about some axis, together with the explicit
axis-angle formula. Topological statements (the cover is a universal cover) are a separate node.

## Sources

- J. Stillwell, *Naive Lie Theory*, Springer, 2008, for quaternions and the rotations of space.
