# Asymptotic for B-free divisor sums in progressions when h is at most 2

Let $F$ be a
finite field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let
$\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every
monic irreducible $P$. Let $m \ne 0$ and $a$ be polynomials in $F[T]$ with $a$ coprime to $m$, let
$h \in \{1, 2\}$, and let $\tilde D_{\kappa,h}(N, a, m)$ be the sum of $d_h(f)$ over the monic
$B_\kappa$-free $f$ of degree at most $N$ with $f \equiv a \pmod m$, where $d_h(f)$ is the number
of $h$-tuples of monic polynomials with product $f$, and $f$ is $B_\kappa$-free when no
$P^{\kappa(P)}$ with $P$ monic irreducible divides it. Put
$C_P = \binom{h + \kappa(P) - 1}{\kappa(P)}$ and

$$
M(N) = \frac{q^N N^{h-1}}{(h-1)!} \cdot
\frac{\bigl(\prod_{P \mid m} (1 - 1/|P|)\bigr)^{h-1}}{|m| \, (1 - 1/q)}
\prod_{P \nmid m} \Bigl(1 - |P|^{-\kappa(P)} \bigl(C_P + |P|^{-1} (1 - C_P)\bigr)\Bigr),
$$

the products running over the monic irreducible $P$ dividing, respectively not dividing, $m$.
Then $\tilde D_{\kappa,h}(N, a, m) - M(N) = O(M(N)/N)$ as $N \to \infty$.

The paper states this for every $h \ge 1$, but its main term is not correct for $h \ge 3$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 4, cases `h = 1, 2`; `Φ` as defined after Theorem 3.
