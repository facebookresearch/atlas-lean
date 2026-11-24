# Two-locus coalescence times of a pair: a diagonal atom and an absolutely continuous part

Let $\rho \ge 0$ and let $(T_A, T_B)$ be the coalescence times at loci $A$ and $B$ of the two-locus coalescent of a sample of two, started from two linked sequences, as on the [path-form covariance page](covariance-coalescence-times.md). The event $\{T_A = T_B\}$ is the event that the chain enters "both coalesced" directly from "linked", and its probability is

$$p(\rho) = \mathbb P(T_A = T_B) = \frac{\rho + 18}{\rho^2 + 13\rho + 18},$$

the solution of the first-step equations $p_{\mathrm L} = \frac{1 + \rho\, p_{\mathrm P}}{1 + \rho}$, $p_{\mathrm P} = \frac{p_{\mathrm L} + (\rho/2)\, p_{\mathrm S}}{3 + \rho/2}$, $p_{\mathrm S} = \frac{2}{3} p_{\mathrm P}$ from the linked, partly split and split states. The law of $(T_A, T_B)$ is

$$p(\rho)\, \mathcal L(T, T) + \bigl(1 - p(\rho)\bigr)\, \mu_\rho,$$

where $T$ has an absolutely continuous law on $(0, \infty)$ and $\mu_\rho$ is absolutely continuous on $\{(s, t) : s \ne t\}$. Hence for almost every $t$ the conditional law of $T_B$ given $T_A = t$ has its only atom at $t$. For $\rho = 0$, $p = 1$ and $T_A = T_B$; for $\rho > 0$, $p(\rho) < 1$.

## Depends on

- [Covariance of the coalescence times, path form](covariance-coalescence-times.md)

## Expansion

A full proof page must still establish:

- the identification of $\{T_A = T_B\}$ with a direct jump from linked to both coalesced, and the first-step equations above;
- absolute continuity of $T$ and of $\mu_\rho$, from the exponential holding times of the chain;
- the disintegration statement for the conditional law of $T_B$ given $T_A$.

## Sources

- R. R. Hudson, "Properties of a neutral allele model with intragenic recombination", *Theoretical Population Biology* 23(2):183–201, 1983, <https://pubmed.ncbi.nlm.nih.gov/6612631/>. The value of $p(\rho)$ is derived above from the rate matrix of the two-locus coalescent.
