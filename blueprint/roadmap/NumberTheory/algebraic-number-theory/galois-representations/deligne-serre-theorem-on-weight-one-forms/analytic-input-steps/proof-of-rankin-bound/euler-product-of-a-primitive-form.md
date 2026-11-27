# Hecke relations and Euler product of a primitive form

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with $\varepsilon(-1) = (-1)^k$, and let
$f = \sum_{n \ge 1} a_n q^n$ be a [primitive form](primitive-forms-of-type-k-epsilon.md) of type $(k, \varepsilon)$ on
$\Gamma_0(N)$. Then $f|T_p = a_p f$ for every prime $p \nmid N$ and $f|U_p = a_p f$ for every prime $p \mid N$, so that, for
all $n \ge 1$,

$$a_{pn} = a_p a_n - \varepsilon(p) p^{k-1} a_{n/p} \quad (p \nmid N), \qquad a_{pn} = a_p a_n \quad (p \mid N),$$

where $a_{n/p} = 0$ when $p \nmid n$. Consequently $a_{mn} = a_m a_n$ for coprime $m$ and $n$, and, as formal power series in
$X$,

$$\sum_{r \ge 0} a_{p^r} X^r = \frac{1}{1 - a_p X + \varepsilon(p) p^{k-1} X^2} \quad (p \nmid N), \qquad \sum_{r \ge 0} a_{p^r} X^r = \frac{1}{1 - a_p X} \quad (p \mid N);$$

so, for every $s$ at which $\sum_n a_n n^{-s}$ converges absolutely,

$$\sum_{n \ge 1} a_n n^{-s} = \prod_{p \mid N} \frac{1}{1 - a_p p^{-s}} \prod_{p \nmid N} \frac{1}{1 - a_p p^{-s} + \varepsilon(p) p^{k-1-2s}}.$$

Here $N$ is the level of the primitive form $f$ itself.
[Rankin's bound](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md) applies this to the primitive form $f_0$ of a
level $M$ that divides the level of the eigenform it starts from, so that there these formulas hold at level $M$, with
the primes dividing $M$ in the place of those dividing $N$.

This is Theorem 3 (i) of Li and formula (1.7.2) of Deligne–Serre. The recursions follow from the eigenvalue equations by
the action of $T_p$ and $U_p$ on $q$-expansions, as the coefficient of $q$ in $f|T_p = a_p f$ is $a_p a_1 = a_p$. By induction
on $r$ they give $a_{p^r n} = a_{p^r} a_n$ for $p \nmid n$, hence multiplicativity, and the power series identities; the Euler
product of an absolutely convergent Dirichlet series with multiplicative coefficients then gives the last formula.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](../../modular-forms-of-type-k-epsilon.md), for cusp forms of type $(k, \varepsilon)$ and the operators $T_p$
- [Primitive forms of type (k, ε) on Γ₀(N)](primitive-forms-of-type-k-epsilon.md)

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- that a newform is an eigenvector of the $U_p$, $p \mid N$: Li shows that $f|U_p$ has the same eigenvalues as $f$ for the
  $T_\ell$, $\ell \nmid N$, so that $f|U_p - a_p f$, whose first coefficient is $0$, is old by her Theorem 2, and is then $0$,
  as a newform has the eigenvalues of no nonzero old form (pp. 294–295, with Lemma 1, p. 287);
- the action (1.6.1)–(1.6.2) of $T_p$ and $U_p$ on $q$-expansions, which turns the eigenvalue equations into the recursions;
- the Euler product of an absolutely convergent Dirichlet series with multiplicative coefficients.

## Sources

- W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315: Lemma 1 and the Fourier expansions of
  $F|U_q$ and $F|T_p$, p. 287; Theorem 2, p. 292; Theorem 3 (i) and its proof, p. 295.
- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): formulas (1.6.1)–(1.6.2) and §1.7, (1.7.1)–(1.7.2), p. 509.
