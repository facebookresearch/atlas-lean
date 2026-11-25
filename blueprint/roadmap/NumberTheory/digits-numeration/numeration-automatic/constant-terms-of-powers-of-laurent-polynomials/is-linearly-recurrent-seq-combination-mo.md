# Linear recurrence of combinations of constant terms modulo $p$

Let $p$ be a prime, let
$P, Q_1, \dots, Q_\ell$ be Laurent polynomials with integer coefficients in $r$ variables, let
$k_1, \dots, k_\ell \in \mathbb{N}$, and let $F \colon (\mathbb{Z}/p\mathbb{Z})^\ell \to X$ be a
map to a set $X$. Write $\operatorname{ct}[f]$ for the constant term of $f$ and, for
$n \in \mathbb{N}$, let
$b_n = F(\operatorname{ct}[P^{n+k_1} Q_1] \bmod p, \dots,
\operatorname{ct}[P^{n+k_\ell} Q_\ell] \bmod p)$.
Suppose $b_n \ne F(0, \dots, 0)$ for some $n$. Then $(b_n)$ is linearly recurrent if and only if
$p \nmid \operatorname{ct}[P^n]$ for all $n \in \mathbb{N}$, and if $p \mid \operatorname{ct}[P^n]$
for some $n$, then the set of $n$ with $b_n = F(0, \dots, 0)$ has natural density $1$.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Corollary 17 (`jis-2026-26.4.2-cor-17`).
