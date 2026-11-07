# The square root of the Green's operator squares to the Green's operator

Let
$G(x, t) = \min(x, t)\,(1 - \max(x, t))$ be the Green's kernel and let $A$ be a linear map from
$L^2([0, 1])$ to itself that is symmetric, $\langle Af, g \rangle = \langle f, Ag \rangle$ for all
$f, g$, and is given by the Green's kernel, $(Af)(x) = \int_{[0, 1]} G(x, t) f(t)\, dt$ for almost
every $x \in [0, 1]$ and every $f$. Let $(b_k)_{k \ge 1}$ be a Hilbert basis of $L^2([0, 1])$
indexed by the positive integers with $b_k(x) = \sqrt{2} \sin(k\pi x)$ for almost every
$x \in [0, 1]$, and let $A^{1/2}$ be the square root of the Green's operator defined from
$(b_k)$. Then $A^{1/2}(A^{1/2} f) = Af$ for every $f \in L^2([0, 1])$.
