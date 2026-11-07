# Convolution of the $B_\kappa$-free indicator with the Möbius function

Let $F$ be a field
and let $\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ne 0$ for
every monic irreducible $P \in F[T]$. Let $\mathbf{1}_{B_\kappa} \colon F[T] \to \mathbb{C}$ be
the indicator function of the $B_\kappa$-free polynomials, let $\mu$ be the Möbius function of
$F[T]$, and write $r^\kappa$ for the $\kappa$-power of a polynomial $r$. Then for every monic
$f \in F[T]$, the Dirichlet convolution of $\mathbf{1}_{B_\kappa}$ and $\mu$ over monic divisors
satisfies

$$(\mathbf{1}_{B_\kappa} * \mu)(f) = \sum_{r} \mu(r),$$

the sum running over the monic $r \in F[T]$ with $r^\kappa = f$.

There is at most one such $r$, so the right side is $\mu(r)$ if $f = r^\kappa$ for a monic $r$,
and $0$ if there is no such $r$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 5 (`integers-2026-A80-lem-5`).
