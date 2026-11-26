# EPPF recursion for allelic partitions of Λ-coalescents

**Setting.** Let $\Lambda$ be a finite non-zero measure on $[0,1]$ and run the $\Lambda$-coalescent on a sample of $n$ genes: while there are $n$ blocks, the jump to $k$ blocks ($1 \le k < n$, so that $n-k+1$ blocks merge) happens at total rate
$$g_{n,k} = \binom{n}{k-1}\int_{[0,1]} x^{n-k-1}(1-x)^{k-1}\,\Lambda(dx), \qquad g_n = \sum_{k=1}^{n-1} g_{n,k}.$$
Superimpose mutations at rate $r = \theta/2$ per lineage under the infinitely-many-alleles model, and let $\Pi^\theta_n$ be the induced exchangeable partition of $\{1,\dots,n\}$ into allelic classes. Its exchangeable partition probability function (EPPF) $p^n_k(n_1,\dots,n_k)$ is the probability of one particular partition with $k$ blocks of sizes $n_1,\dots,n_k$. Write $\rho_n = g_n + nr$, $\boldsymbol n - i\boldsymbol e_j$ for the block sizes with $n_j$ decreased by $i$, and $\tilde{\boldsymbol n}_j$ for $\boldsymbol n$ with the singleton block $j$ removed.

**Theorem.** $p^1_1(1) = 1$ and, for $n \ge 2$ and every composition $\boldsymbol n = (n_1,\dots,n_k)$ of $n$,
$$p^n_k(\boldsymbol n) = \frac{r}{\rho_n}\sum_{j:\,n_j = 1} p^{n-1}_{k-1}(\tilde{\boldsymbol n}_j) + \sum_{i=1}^{n-1}\frac{g_{n,n-i}}{\rho_n}\sum_{j:\,n_j > i}\frac{n_j - i}{n-i}\,\frac{\binom{n_j}{i}}{\binom{n}{i}}\,p^{n-i}_k(\boldsymbol n - i\boldsymbol e_j).$$
Conversely, this recursion together with $p^1_1(1) = 1$ determines $p^n_k$ uniquely. In terms of the moments $h_j = \int_{[0,1]}(1-x)^j\,\Lambda(dx)$ one has $g_{n,n-1} = \binom{n}{2}h_{n-2}$ and $g_n = \sum_{j=0}^{n-2}(j+1)h_j$.

## Expansion

Look backwards from the sample to the first event. With $n$ lineages, the next event is a mutation with probability $nr/\rho_n$ and a merger of $i+1$ lineages with probability $g_{n,n-i}/\rho_n$. A mutation on a lineage makes it a singleton allelic class and removes it from further consideration (it carries a new allele). A merger of $i+1$ lineages is consistent with the observed partition only if all of them lie in the same allelic block; the combinatorial factor counts the ways to choose them and converts Möhle's recursion for sampling probabilities of allele-count vectors into one for the EPPF. For Kingman's coalescent ($\Lambda = \delta_0$) only $i = 1$ survives and the recursion is solved by the Ewens sampling formula.

## Sources

- R. R. Albuquerque, A. M. S. Macêdo, R. Ospina, "Gibbs-type allelic partitions of Λ-coalescents: a rigidity theorem", arXiv:2611.30994 (2026), Theorem 3.2 and Lemma 2.1, <https://doi.org/10.48550/arXiv.2611.30994>.
