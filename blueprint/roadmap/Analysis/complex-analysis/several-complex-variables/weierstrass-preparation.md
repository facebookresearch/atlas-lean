# Weierstrass preparation theorem

Let $E$ be a finite-dimensional normed vector space over
$\mathbb{C}$ and let $f : E \times \mathbb{C} \to \mathbb{C}$ be analytic at $0$. Suppose that for
some $d \in \mathbb{N}$ and some $g : \mathbb{C} \to \mathbb{C}$ analytic at $0$ with $g(0) \ne 0$,
$f(0, w) = w^d g(w)$ for all $w$ in a neighbourhood of $0$. Then there are functions
$a_0, \dots, a_{d-1} : E \to \mathbb{C}$, each analytic at $0$ with $a_j(0) = 0$, a function
$u : E \times \mathbb{C} \to \mathbb{C}$ analytic at $0$ with $u(0) \ne 0$, and an open set
$U \subseteq E \times \mathbb{C}$ containing $0$ such that
$f(z, w) = u(z, w) \bigl(w^d + \sum_{j=0}^{d-1} a_j(z) w^j\bigr)$ for all $(z, w) \in U$.

## Sources

- Weierstrass preparation theorem in several complex variables; see Hörmander. The statement here is the form on a product $E \times \mathbb{C}$ with $E$ finite-dimensional, for a function of order $d$ on the slice: near the origin it factors as a unit times a Weierstrass polynomial of degree $d$ in $w$ whose lower coefficients vanish at the origin.
