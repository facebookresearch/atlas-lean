# Uniform deviation of the empirical risk over a finite class

Let $z_1, \dots, z_n$, with $n \ge 1$, be independent examples with common law $\nu$, let $F$ be a finite class of predictors, and let the loss satisfy $L(f, z) \in [0, \ell_\infty]$ for $\nu$-almost every $z$, with $z \mapsto L(f, z)$ measurable for each $f$. Then for every $t \ge 0$,

$$
\mathbb{P}\big(\exists f \in F,\ |\hat R(f) - R(f)| \ge t\big) \le 2 |F| \exp\Big(-\frac{2 n t^2}{\ell_\infty^2}\Big),
$$

with a quotient by $0$ read as $0$. Proof: for each $f$ the losses $L(f, z_i)$ are independent, lie in $[0, \ell_\infty]$ and have mean $R(f)$, so the two-sided Hoeffding inequality bounds each deviation event; a union bound over the $|F|$ predictors gives the result.

It is the bound of [Uniform deviation for a finite class](finite-class-uniform-deviation.md) for an arbitrary bounded loss and with the non-strict event.

## Background

- [Uniform deviation for a finite class](finite-class-uniform-deviation.md): background, the exposition of the same bound and of its use for empirical risk minimization.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 4.4.3 (finite number of models), and Section 1.2.1, Corollary 1.1.
