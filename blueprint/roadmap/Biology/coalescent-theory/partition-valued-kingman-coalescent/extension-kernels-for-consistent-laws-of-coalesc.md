# Extension kernels for consistent laws of coalescent paths

Fix a finite nonnegative time grid $0 \le t_1 < \dots < t_k$ and, for each $n$, let $\mu_n$ be a probability measure on the finite set of
$n$-paths, sequences $\rho = (\rho_1, \dots, \rho_k)$ of partitions of $\{1, \dots, n\}$. Write $\rho = \pi|_n$
when restricting each $\pi_i$ to $\{1, \dots, n\}$ gives $\rho_i$, and assume the consistency
$\mu_n(\rho) = \sum_{\pi|_n = \rho} \mu_{n+1}(\pi)$. Define $\kappa_n(\rho, \pi) = \mu_{n+1}(\pi) / \mu_n(\rho)$ if
$\pi|_n = \rho$ and $\mu_n(\rho) > 0$, $\kappa_n(\rho, \pi) = 0$ if $\pi|_n \ne \rho$, and, if $\mu_n(\rho) = 0$, let
$\kappa_n(\rho, \cdot)$ be the point mass at the path that adds $n + 1$ as a singleton block at every time.
Then:

1. each $\kappa_n(\rho, \cdot)$ is a probability measure supported on paths $\pi$ with $\pi|_n = \rho$;
2. $\sum_\rho \mu_n(\rho)\, \kappa_n(\rho, \pi) = \mu_{n+1}(\pi)$ for every $(n + 1)$-path $\pi$.

For (1), the rows with $\mu_n(\rho) > 0$ sum to $1$ by consistency, and the other rows are point masses on
an extension of $\rho$. For (2), only $\rho = \pi|_n$ contributes; if $\mu_n(\pi|_n) > 0$ the term is
$\mu_{n+1}(\pi)$, and if $\mu_n(\pi|_n) = 0$ then $\mu_{n+1}(\pi) \le \mu_n(\pi|_n) = 0$ and the term is $0$. For
Kingman's coalescent the laws $\mu_n$ of $(X^n_{t_1}, \dots, X^n_{t_k})$ are consistent by
[restriction consistency of the path laws](strong-path-level-restriction-consistency-of-the.md), and the kernels build the joint law of all
restrictions sample size by sample size.

## Proof depends on

- [Path laws of Kingman's coalescent on a finite sample are consistent under restriction](strong-path-level-restriction-consistency-of-the.md)

For an explicit $n=1$ to $n=2$ example at one time $t\ge0$, the one-lineage space has only one state $\rho$. Writing $S$ for two singletons and $C$ for their merger,

$$\kappa_1(\rho,S)=e^{-t},\qquad \kappa_1(\rho,C)=1-e^{-t}.$$

At a grid containing time $0$, a nonsingleton initial state has zero probability; a path that splits blocks also has zero probability. Both still receive the specified compatible point-mass row, so the kernel is defined on all inputs.

## Sources

- J. F. C. Kingman, "The coalescent", Stochastic Processes and their Applications 13 (1982), 235–248, <https://doi.org/10.1016/0304-4149(82)90011-4>, Section 4 (consistency of the $n$-coalescents, the property this lemma disintegrates). The lemma is a finite disintegration derived above and is not stated in the source.
