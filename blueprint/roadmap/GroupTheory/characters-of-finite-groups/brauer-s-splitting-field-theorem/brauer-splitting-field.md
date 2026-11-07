# Brauer's splitting field theorem

Let $G$ be a finite group of exponent $n$, let
$K = \mathbb{Q}(\zeta_n)$ be the $n$-th cyclotomic field, and let $\rho$ be a representation of
$G$ on a finite-dimensional complex vector space $V$. Then there are a ring homomorphism
$\varphi \colon K \to \mathbb{C}$, a $K$-vector space $W$ with a representation $\sigma$ of $G$
on $W$, and a $\mathbb{C}$-linear isomorphism $f \colon \mathbb{C} \otimes_K W \to V$, where
$\mathbb{C}$ is regarded as a $K$-algebra via $\varphi$, such that
$f((\mathrm{id}_{\mathbb{C}} \otimes \sigma(g))(x)) = \rho(g)(f(x))$ for all $g \in G$ and all
$x \in \mathbb{C} \otimes_K W$.

## Sources

- R. Brauer, On the representation of a group of order g in the field of g-th roots of unity, Amer. J. Math. 67 (1945), 461–471. Via leanprover/lean-eval@38361be, problem `brauer_splitting_field`.
