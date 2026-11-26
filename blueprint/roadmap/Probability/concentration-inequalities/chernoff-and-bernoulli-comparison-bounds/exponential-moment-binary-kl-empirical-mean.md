# Exponential moment of the binary relative entropy of an empirical Bernoulli mean

Let $n \ge 1$ and let $X_1, \dots, X_n$ be i.i.d. Bernoulli($p$) random variables (values in $\{0,1\}$, as for a binary loss), and let $\hat p = \frac1n\sum_i X_i$. Then

$$
\mathbb{E}\Big[\exp\big(n\, \mathrm{kl}(\hat p \,\|\, p)\big)\Big] \le n + 1,
$$

where $\mathrm{kl}$ is the binary relative entropy in nats.

## Proof sketch

Since $n\hat p$ is binomial with parameters $n$ and $p$, the expectation equals $\sum_{k=0}^n \binom nk p^k(1-p)^{n-k}\exp(n\,\mathrm{kl}(k/n\|p))$. Each term is at most $1$ by the binomial-mass bound, and there are $n+1$ terms.

## Depends on

- [Binary relative entropy](../../../InformationTheory/information-inequalities/binary-relative-entropy/binary-relative-entropy.md)

## Proof depends on

- [Binomial probabilities are bounded by the exponential of binary relative entropy](../../../InformationTheory/information-inequalities/binary-relative-entropy/binomial-mass-binary-kl-bound.md)

## Sources

- M. Seeger, "PAC-Bayesian Generalisation Error Bounds for Gaussian Process Classification", Journal of Machine Learning Research 3, 2002, Theorem 1 and its proof in Appendix A.
