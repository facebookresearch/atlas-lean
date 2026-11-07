# Twin prime asymptotic over $\mathbb{F}_q(T)$ for large $q$

Let $p$ be an odd prime and let
$q$ be a power of $p$ with $q > 685090\,p^2$; write $\mathbb{F}_q$ for the finite field with $q$
elements. Then there is a real number $\varepsilon > 0$ such that for every nonzero
$h \in \mathbb{F}_q[T]$, as $X \to \infty$ through the powers of $q$,

$$\#\{f \in \mathbb{F}_q[T] : |f| = X,\ f \text{ and } f + h \text{ are prime}\} =
\frac{\mathfrak{S}_q(h)\, X}{(\log_q X)^2} + O\bigl(X^{1 - \varepsilon}\bigr),$$

where $|f| = |\mathbb{F}_q[T]/(f)|$ is the norm of $f$, the primes of $\mathbb{F}_q[T]$ are its
monic irreducible polynomials, $\mathfrak{S}_q(h)$ is the singular series for twin primes, and
the implied constant may depend on $h$ (but $\varepsilon$ does not).

## Sources

- W. Sawin and M. Shusterman, `On the Chowla and twin primes conjectures over 𝔽_q[T]`, Annals of Math, 196 (2) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-196-2-ChowlaAndTwinPrimeOverFqT.lean Via leanprover/lean-eval@38361be, problem `annals_chowla_and_twin_prime_over_fq_t`.
