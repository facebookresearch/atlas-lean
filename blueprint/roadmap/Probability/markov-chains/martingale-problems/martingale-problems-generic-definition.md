# Martingale problems

Let $E$ be a metric space (for example a compact one such as $[0,1]$ or a simplex), let $A$ be a linear operator with domain $\mathcal D(A)$ in the bounded measurable functions on $E$ and values bounded measurable (typically $\mathcal D(A)\subseteq C(E)$ and $Af\in C(E)$), and let $\mu$ be a probability measure on $E$. A process $X=(X_t)_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$ with a filtration $(\mathcal F_t)$ **solves the $(A,\mu)$ martingale problem** with respect to $(\mathcal F_t)$ if

1. $X$ is $(\mathcal F_t)$-adapted, with paths in a stated class: continuous, or càdlàg;
2. $X_0$ has law $\mu$;
3. for every $f\in\mathcal D(A)$,

    $$M^f_t=f(X_t)-f(X_0)-\int_0^tAf(X_s)\,ds$$

    is an $(\mathcal F_t)$-martingale.

A solution with respect to some filtration is a solution with respect to the natural filtration of $X$. The **graph** of $A$ is $\{(f,Af):f\in\mathcal D(A)\}$; a martingale problem may equally be posed for a set of pairs $(f,g)$, with $g$ in place of $Af$. **Uniqueness** holds for $(A,\mu)$ if any two solutions, possibly on different probability spaces, have the same finite-dimensional distributions; the martingale problem is **well posed** in the stated path class if for every initial law $\mu$ a solution exists and uniqueness holds.

For $E=[0,1]$, continuous paths, test functions $C^2$ and $A=L_\sigma$ the Wright–Fisher backward generator with scaled selection coefficient $\sigma$, this is the [martingale problem for the Wright–Fisher diffusion](../../../Biology/population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md).

## Proof depends on

- [General optional stopping for uniformly integrable martingales](../../martingales/optional-stopping-theorem/integral-stopped-value-at-top-eq-of-unif.md)
- [Filtrations and stopping times](../../martingales/stopping-times-and-martingale-problems/filtrations-and-stopping-times.md)

## Expansion

A full definition page must fix:

- The path class and the measurability of $X$ needed for the time integral (càdlàg or continuous paths suffice).
- The equivalence between solutions with respect to a filtration and with respect to the natural filtration.
- The bridge to the Wright–Fisher instance: a process solves the Wright–Fisher martingale problem with parameter $\sigma$ exactly when it solves the generic problem for $A=L_\sigma$ on $C^2$ test functions (a $C^2$ function on $\mathbb R$ and its restriction to $[0,1]$ give the same compensated process).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4 (martingale problems).
- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Grundlehren 233, Springer (1979), <https://books.google.com/books?id=vKC1BwAAQBAJ> (the martingale-problem formulation).
