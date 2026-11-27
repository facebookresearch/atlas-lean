# Success probability of a mutant lineage in a fitness valley

Consider an asexual population in which a beneficial genotype requires $K \ge 2$ mutations acquired in a fixed order. An individual carrying $k$ of them has fitness $w_0 = 1$, $w_k = 1 - \delta_k$ with $0 \le \delta_k < 1$ for $1 \le k \le K-1$, and $w_K = 1 + s$, and it mutates to the next genotype at rate $\mu_k$. While all intermediate genotypes are rare, a $k$-mutant lineage is modelled as a continuous-time branching process in which each individual dies at rate $1$, divides into two $k$-mutants at rate $1-\delta_k$, and produces a $(k+1)$-mutant offspring at rate $\mu_k$.

Call a $k$-mutant *successful* if some descendant is a $K$-mutant whose lineage establishes, and let $p_k$ be the probability of success, with $p_K \approx s$ for $1/N \ll s \ll 1$. Then, for $1 \le k \le K-1$,

$$p_k = \frac{-\delta_k - \mu_k p_{k+1} + \sqrt{(\delta_k - \mu_k p_{k+1})^2 + 4 \mu_k p_{k+1}}}{2(1-\delta_k)}.$$

When $\mu_k p_{k+1} \ll 1$ this is approximately

$$p_k \approx \frac{-\delta_k + \sqrt{\delta_k^2 + 4\mu_k p_{k+1}}}{2} \approx \begin{cases} \sqrt{\mu_k p_{k+1}}, & \delta_k \ll 2\sqrt{\mu_k p_{k+1}},\\ \mu_k p_{k+1}/\delta_k, & \delta_k \gg 2\sqrt{\mu_k p_{k+1}}. \end{cases}$$

Iterating from $p_K = s$ gives, when all intermediates are effectively neutral,

$$p_1 \approx s^{1/2^{K-1}} \prod_{j=1}^{K-1} \mu_j^{1/2^j},$$

and when all intermediates are strongly deleterious,

$$p_1 \approx s \prod_{j=1}^{K-1} \frac{\mu_j}{\delta_j}.$$

The formulas assume the population is large enough that a $k$-mutant lineage does not drift to a high frequency before succeeding.

## Proof sketch

First-step analysis on one $k$-mutant. The four possible first events occur at total rate $2 - \delta_k + \mu_k$: death (rate $1$, success probability $0$), division (rate $1-\delta_k$, success probability $1-(1-p_k)^2$), production of a successful $(k+1)$-mutant (rate $\mu_k p_{k+1}$, success probability $1$), and production of an unsuccessful one (rate $\mu_k(1-p_{k+1})$, after which the original individual still has success probability $p_k$). Equating gives the quadratic $(1-\delta_k)p_k^2 + (\delta_k + \mu_k p_{k+1})p_k - \mu_k p_{k+1} = 0$, whose nonnegative root is the displayed formula, using $(\delta+\mu p)^2 + 4(1-\delta)\mu p = (\delta-\mu p)^2 + 4\mu p$. The neutral limit says a successful neutral lineage must drift to size about $1/\sqrt{\mu_k p_{k+1}}$, which a critical branching process does with probability of that order; the deleterious limit says a lineage survives about $1/\delta_k$ generations and must produce a successful mutant in that time.

## Sources

- D. B. Weissman, M. M. Desai, D. S. Fisher, M. W. Feldman, *The rate at which asexual populations cross fitness valleys*, Theoretical Population Biology 75 (2009), 286–300, <https://doi.org/10.1016/j.tpb.2009.02.006>, PMCID PMC2992471. Model in Eq. (1) and Section II; recursion Eqs. (12)–(15); first-step derivation Eq. (50), Appendix C.
