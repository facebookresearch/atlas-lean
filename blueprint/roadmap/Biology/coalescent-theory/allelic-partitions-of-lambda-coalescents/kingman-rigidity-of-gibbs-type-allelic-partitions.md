# Kingman rigidity of Gibbs-type allelic partitions

**Setting.** An exchangeable random partition of $\{1,\dots,n\}$ is of *Gibbs type* with index $\sigma \in [0,1)$ if its EPPF factorizes as

$$p^n_k(n_1,\dots,n_k) = V_{n,k}\prod_{j=1}^k (1-\sigma)_{n_j - 1}, \qquad V_{n,k} \ge 0,$$

where $(a)_m = a(a+1)\cdots(a+m-1)$; the Ewens sampling formula ($\sigma = 0$) and the two-parameter Poisson–Dirichlet partitions are examples. Let $\Pi^\theta_n$ be the allelic partition of a sample of size $n$ whose genealogy is the $\Lambda$-coalescent ($\Lambda$ a finite non-zero measure on $[0,1]$), with infinitely-many-alleles mutation at rate $\theta > 0$.

**Theorem.** The following are equivalent:
1. $\Pi^\theta_n$ is of Gibbs type for some index $\sigma \in [0,1)$ (for every $n$);
2. $\Lambda = c\,\delta_0$ for some $c > 0$, i.e. the genealogy is a time-changed Kingman coalescent;
3. the EPPF of $\Pi^\theta_n$ is the Ewens sampling formula with parameter $\vartheta = \theta/c$:

$$p^n_k(n_1,\dots,n_k) = \frac{\vartheta^k}{(\vartheta)_n}\prod_{j=1}^k (n_j - 1)!.$$

In every case the index is $\sigma = 0$. The obstruction is already finite: if $\Lambda$ is not concentrated at $0$, the allelic law on a sample of six genes admits no Gibbs factorization with a common index $\sigma < 1$ (nor with $\sigma = -\infty$). Gibbs indices $\sigma < 0$ are excluded for every $\Lambda$.

## Expansion

Plugging the Gibbs ansatz into the EPPF recursion of the $\Lambda$-coalescent gives a linear "master system" for the weights $V_{n,k}$, which must hold for every block configuration of the same size. Organizing the constraints by the sector $d = n - k$: $d = 0$ fixes $V_{n,n}$, $d = 1$ is automatically consistent for every $\Lambda$, and $d = 2$ yields a scalar identity in the moments $h_j = \int(1-x)^j\Lambda(dx)$ that determines a unique candidate index from $n = 3$ data. For $\sigma = 0$ complete monotonicity of $(h_j)$ forces $h_j$ constant, i.e. $\Lambda = c\delta_0$; positive indices are excluded by an exact polynomial-positivity certificate for the $d = 3$ sector at sample size six. So among all exchangeable coalescents with mutation, only Kingman's produces a "Chinese restaurant"–type predictive rule.

## Depends on

- [EPPF recursion for allelic partitions of Λ-coalescents](eppf-recursion-for-allelic-partitions-of-lambda-coalescents.md)

## Sources

- R. R. Albuquerque, A. M. S. Macêdo, R. Ospina, "Gibbs-type allelic partitions of Λ-coalescents: a rigidity theorem", arXiv:2611.30994 (2026), Theorem 4.6, Theorem 5.12 and Corollaries 5.13, 5.15, <https://doi.org/10.48550/arXiv.2611.30994>.
