# The Galton–Watson martingale and its finite-variance limit

Let the [labelled Galton–Watson tree](ulam-harris-labelled-galton-watson-trees-and-pro.md)
have offspring law $\nu$ on $\mathbb N$, started from one root, with
[mean offspring number](mean.md) $0<m<\infty$.
For its generation sizes $Z_n$ and finite-level filtration $\mathcal F_n$,
$W_n=Z_n/m^n$ is a nonnegative martingale, $\mathbb E Z_n=m^n$, and
$W_n$ converges almost surely to a finite nonnegative limit $W$.
If $q$ is the [extinction probability](extinction-prob.md), then
$\mathbb P(W=0)\in\{q,1\}$, including the deterministic one-child case.

If $m>1$ and $\sigma^2=\operatorname{Var}L<\infty$, then

$$\operatorname{Var}W_n=\frac{\sigma^2(1-m^{-n})}{m(m-1)},\qquad
 W_n\longrightarrow W\text{ in }L^2,\qquad
 \mathbb EW=1,\quad\operatorname{Var}W=\frac{\sigma^2}{m(m-1)}.$$

For Poisson offspring with mean two, $\operatorname{Var}W_n=1-2^{-n}$
and $\operatorname{Var}W=1$.

## Depends on

- [Labelled Galton–Watson tree and generation counts](ulam-harris-labelled-galton-watson-trees-and-pro.md)
- [Mean offspring number](mean.md)
- [Extinction probability](extinction-prob.md)

## Proof depends on

- [Martingale almost-sure convergence](../../martingales/martingale-convergence-theorems/exists-ae-tendsto-of-pos-part-bdd-2.md)
- [The Lp martingale convergence theorem](../../martingales/martingale-convergence-theorems/tendsto-e-lp-norm-limit-process-of-e-lp.md)
- [Extinction probability as the least fixed point](is-least-extinction-prob.md)
- [Galton–Watson extinction criterion](extinction-prob-eq-one-iff.md)

## Expansion

The conditional offspring sum gives
$\mathbb E[Z_{n+1}\mid\mathcal F_n]=mZ_n$. Induction establishes
integrability and the mean formula, hence the martingale property.
Nonnegative martingale convergence applies with $\mathbb EW_n=1$.

To prove the zero-probability dichotomy, descendant-tree limits are
independent copies $W_i$, independent of the root offspring number $L$,
and $W=m^{-1}\sum_{i=1}^L W_i$. Thus
$r=\mathbb P(W=0)$ satisfies $r=f(r)$ for the offspring generating
function $f$, and $r\ge q$ because extinction forces $W=0$.
If $\nu=\delta_1$, then $W=1$ and $q=0$. Otherwise, for $m\le1$
the extinction criterion gives $q=1$. For $m>1$, $f-s$ is strictly convex
on $(0,1)$, since the offspring law has positive mass above one. Its only
zeros in $[q,1]$ are $q,1$, proving the dichotomy.

With finite variance, conditional variance and expectation give
$\operatorname{Var}Z_{n+1}=m^2\operatorname{Var}Z_n+\sigma^2m^n$, hence
$\operatorname{Var}W_{n+1}-\operatorname{Var}W_n=\sigma^2m^{-n-2}$.
Summing the geometric series proves the finite-time formula and a uniform
L2 bound. L2 martingale convergence yields the stated limit moments.

## Sources

- R. Lyons and Y. Peres, *Probability on Trees and Networks*, corrected edition of August 19, 2026, <https://rdlyons.pages.iu.edu/prbtree/book.pdf>, Section 5.1, Propositions 5.4--5.5, Corollary 5.7 and the finite-second-moment remark after the Kesten--Stigum statement. The variance and fixed-point arguments are explicit above.
