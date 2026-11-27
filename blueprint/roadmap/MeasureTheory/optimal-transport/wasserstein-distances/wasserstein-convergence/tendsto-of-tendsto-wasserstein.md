# Convergence in Wasserstein distance implies weak convergence

On a second-countable pseudo-extended metric space whose σ-algebra contains the open sets, let
$p \ge 1$ and let $\mu_k$, $\mu$ be probability measures. If $W_p(\mu_k, \mu) \to 0$, then $\mu_k \to \mu$
weakly.

Proof: for a bounded $L$-Lipschitz $f$,
$|\int f\,d\mu_k - \int f\,d\mu| \le L\, W_1(\mu_k, \mu) \le L\, W_p(\mu_k, \mu) \to 0$, and convergence of
the integrals of bounded Lipschitz functions characterises weak convergence (portmanteau theorem).

This is the part "$W_p(\mu_k, \mu) \to 0$ implies $\mu_k \to \mu$" of
[Theorem 6.9](tendsto-wasserstein-iff.md), which also gives the convergence of $p$-th moments and the
converse.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Theorem 6.9 and Definition 6.8.
