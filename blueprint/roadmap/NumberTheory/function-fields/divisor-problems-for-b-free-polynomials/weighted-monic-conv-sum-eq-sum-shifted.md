# Weighted convolution sums as sums of shifted sums

Let $F$ be a finite field and let
$\gamma, \alpha, \beta$ be functions from $F[T]$ to $\mathbb{C}$. Write $\alpha * \beta$ for the
monic Dirichlet convolution, $\mu$ for the Möbius function of $F[T]$, and $\lambda = \gamma * \mu$.
For a natural number $n$ let $M_{\le n}$ be the set of monic polynomials in $F[T]$ of degree at
most $n$, let $D(\gamma, \alpha, \beta; n) = \sum_{f \in M_{\le n}} \gamma(f)\,(\alpha * \beta)(f)$
and, for monic $f$, let
$S_f(\alpha, \beta; n) = \sum_{g \text{ monic},\ \deg f + \deg g \le n} (\alpha * \beta)(fg)$.
Then

$$D(\gamma, \alpha, \beta; n) = \sum_{f \in M_{\le n}} \lambda(f)\, S_f(\alpha, \beta; n).$$

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 4.
