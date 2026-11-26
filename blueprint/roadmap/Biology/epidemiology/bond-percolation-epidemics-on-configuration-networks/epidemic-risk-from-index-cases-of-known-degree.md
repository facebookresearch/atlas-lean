# Epidemic risk from index cases of known degree

Work in the setting of [bond percolation on a configuration-model network](outbreak-size-and-epidemic-probability-under-bond-percolation.md): degree distribution $(p_k)$, excess-degree generating function $G_1$, transmissibility $T$, and $u$ the smallest root of $u = G_1(1 + (u-1)T)$.

**Statements.**

1. *Index case of degree $k$.* The probability that a single index case of degree $k$ starts a large epidemic is

$$\varepsilon_k = 1 - (1 - T + Tu)^k,$$

which is increasing in $k$.
2. *Several index cases.* If $N$ cases with degrees $k_1, \dots, k_N$ are currently infected (and their onward chains are asymptotically independent), the probability that at least one of them ignites an epidemic is

$$1 - \prod_{i=1}^{N} (1 - \varepsilon_{k_i}).$$

If only the number $N$ of current cases is known, each having been infected along an edge, the probability is

$$1 - \left(\frac{\sum_k k p_k (1 - T + Tu)^{k-1}}{\sum_k k p_k}\right)^{N} = 1 - G_1(1 - T + Tu)^N.$$

3. *Individual risk during an epidemic.* Conditional on a large epidemic, a vertex of degree $k$ is infected with probability

$$\nu_k = 1 - (1 - T + Tu)^k = \varepsilon_k .$$

## Depends on

- [Outbreak size and epidemic probability under bond percolation on a configuration-model network](outbreak-size-and-epidemic-probability-under-bond-percolation.md)

## Expansion

Along any one edge out of an infected vertex the infection either is not transmitted (probability $1-T$) or is transmitted to a vertex whose own subtree dies out (probability $Tu$); edges behave independently in the tree-like limit, which gives $\varepsilon_k$. A case infected along an edge has $k-1$ further edges with the size-biased probability $k p_k / \langle k \rangle$, which gives the excess-degree version of statement 2. For statement 3, a neighbour fails to infect the focal vertex either because it was never infected ($u$) or because it was infected but did not transmit ($(1-u)(1-T)$); the sum is $1 - T + Tu$, and the identity $\nu_k = \varepsilon_k$ reflects the symmetry between being reached by and reaching the giant percolation cluster. These formulas quantify why superspreading individuals of high degree dominate both the risk of starting and the risk of catching an epidemic.

## Sources

- Meyers LA, Pourbohloul B, Newman ME, Skowronski DM, Brunham RC, "Network theory and SARS: predicting outbreak diversity" (2005), Section "Epidemiological analysis" (formulas for $\varepsilon_k$, the $N$-case ignition probability and $\nu_k$), <https://doi.org/10.1016/j.jtbi.2004.07.026>, PMCID PMC7094100.
