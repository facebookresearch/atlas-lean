# Asymptotic for the B-free divisor function in an arithmetic progression

Let $F$ be a
finite field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let
$\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every
monic irreducible $P$; let $\kappa_{\min}$ be the minimum of $\kappa(P)$ over the monic
irreducible $P$. Let $m \ne 0$ and $a$ be polynomials in $F[T]$ with $a$ coprime to $m$, and let
$\tilde D_{\kappa,2}(N, a, m)$ be the sum of $d_2(f)$ over the monic $B_\kappa$-free $f$ of degree
at most $N$ with $f \equiv a \pmod m$, where $d_2(f)$ is the number of pairs of monic polynomials
with product $f$, and $f$ is $B_\kappa$-free when no $P^{\kappa(P)}$ with $P$ monic irreducible
divides it. Writing $\kappa$ for $\kappa(P)$ inside sums and products over $P$, put

$$
M(N) = \frac{q^N}{(1 - 1/q) \, |m|} \prod_{P \mid m} \Bigl(1 - \frac{1}{|P|}\Bigr)
\prod_{P \nmid m} \Bigl(1 - \frac{\kappa + 1}{|P|^{\kappa}} + \frac{\kappa}{|P|^{\kappa + 1}}\Bigr)
\times \Bigl(N + 1 - \frac{1}{q - 1} + 2 \sum_{P \mid m} \frac{\deg P}{|P| - 1} +
\sum_{P \nmid m}
\frac{\kappa (\kappa + 1) \deg P \, (|P| - 1)}{|P|^{\kappa + 1} - |P| (\kappa + 1) + \kappa}\Bigr),
$$

where $P$ runs over the monic irreducible polynomials dividing, respectively not dividing, $m$.
Then for every $\varepsilon > 0$,
$\tilde D_{\kappa,2}(N, a, m) - M(N) = O\bigl(q^{(1/\kappa_{\min} + \varepsilon) N}\bigr)$ as
$N \to \infty$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 3, second formula; `Φ` as defined after Theorem 3.
