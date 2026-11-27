# Fraser's Fourier decay theorem for finite-field Kakeya sets

Let $F$ be a finite field
with $q$ elements, let $d \ge 2$ be a natural number, let $K \subseteq F^d$ be a Kakeya set and let
$\chi$ be a nontrivial additive character of $F$ with values in $\mathbb{C}$. Then, first, there is
a probability measure $\mu$ on $K$ whose Fourier transform $\hat{\mu}$ with respect to $\chi$
satisfies $|\hat{\mu}(\xi)| \le q^{-1}$ for every nonzero $\xi \in F^d$. Second, this bound is
sharp: for every real $\kappa$ with $0 < \kappa < 1$ there is a natural number $Q$ such that for
every finite field $F'$ with $q' \ge Q$ elements there is a Kakeya set $K' \subseteq (F')^d$ such
that every probability measure $\mu$ on $K'$ has a nonzero $\xi \in (F')^d$ at which its Fourier
transform $\hat{\mu}$ with respect to a fixed primitive additive character of $F'$ satisfies
$|\hat{\mu}(\xi)| \ge \kappa \, q'^{-1}$.

## Sources

- J.M. Fraser, 'Fourier analytic properties of Kakeya sets in finite fields', Bull. London Math. Soc. 58(5) (2026); DOI 10.1112/blms.70367; arXiv:2505.09464. Problem `fraser_kakeya_fourier_decay` of the lean-eval benchmark.
