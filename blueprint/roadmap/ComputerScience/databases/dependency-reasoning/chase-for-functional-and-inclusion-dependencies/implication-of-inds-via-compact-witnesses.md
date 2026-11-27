# Implication of inclusion dependencies via compact witnesses

For an inclusion dependency $\sigma' = R'[\alpha] \subseteq P'[\beta]$ and a tuple of variables $\bar x$, let
$\mathrm{new}_\star(\sigma', \bar x)$ be $\mathrm{new}(\sigma', \bar x)$ with every fresh variable replaced by one placeholder
variable $\star$. For $\sigma = R[i_1, \dots, i_k] \subseteq P[j_1, \dots, j_k]$ and a set $\Sigma$ of inclusion dependencies, all of arity at
least $1$ as on the [chase page](the-chase-for-inclusion-dependencies.md), a
*witness* of $\sigma$ relative to $\Sigma$ is a sequence of atoms $R_1(\bar x_1), \dots, R_n(\bar x_n)$, $n \ge 1$, such that
$R_1(\bar x_1)$ is the atom $R(x_1, \dots, x_{\mathrm{ar}(R)})$ of distinct variables, each $R_i(\bar x_i)$ with $i \ge 2$ equals
$\mathrm{new}_\star(\sigma_i, \bar x_{i-1})$ for some $\sigma_i \in \Sigma$ applicable to $\{R_{i-1}(\bar x_{i-1})\}$, $R_n = P$,
and $\pi_{(i_1, \dots, i_k)}(\bar x_1) = \pi_{(j_1, \dots, j_k)}(\bar x_n)$.

**Lemma.** $\mathrm{Chase}(S_\sigma, \Sigma) \models \sigma$ if and only if there is a witness of $\sigma$ relative to $\Sigma$. A
witness uses at most $\mathrm{ar}(R) + 1$ variables, so its existence can be searched for nondeterministically in polynomial
space, which gives the upper bound of
[the PSPACE-completeness of implication](../implication-of-inclusion-dependencies-is-pspace-complete.md).

## Depends on

- [The chase for inclusion dependencies](the-chase-for-inclusion-dependencies.md)
- [Unrestricted implication of inclusion dependencies via the chase](unrestricted-implication-of-inds-via-the-chase.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, definition of witnesses before Algorithm 2, Algorithm 2 and Lemma 11.13 (pp. 83–84).
