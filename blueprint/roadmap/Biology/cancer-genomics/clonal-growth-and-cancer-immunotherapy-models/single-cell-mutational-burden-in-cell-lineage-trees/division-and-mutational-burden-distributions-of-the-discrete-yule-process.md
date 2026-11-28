# Division and mutational burden distributions of the discrete-time Yule process

**Model.** Start from one mutation-free progenitor cell. At each step $i = 0, 1, 2, \dots$ a cell chosen uniformly at random among the living cells divides (pure birth, so after $i$ steps there are $N_i = i + 1$ cells). At each division the two daughters inherit all mutations of the mother and each acquires $U_1, U_2 \sim \mathrm{Pois}(\mu)$ new mutations, all distinct (infinite sites). For a cell, its *division count* $\ell$ is the number of divisions on its lineage from the root (its leaf depth in the cell lineage tree) and its *mutational burden* $k$ is the number of mutations it carries. Let $D_{\ell,i}$ be the number of cells with division count $\ell$ (the division distribution, DD) and $B_{k,i}$ the number of cells with burden $k$ (the single-cell mutational burden distribution, MBD) at step $i$.

**Proposition.** Let $\left[{i \atop \ell}\right]$ denote the unsigned Stirling numbers of the first kind, $\left[{i+1 \atop \ell}\right] = i\left[{i \atop \ell}\right] + \left[{i \atop \ell-1}\right]$ with $\left[{1 \atop 1}\right] = 1$ and $\left[{i \atop \ell}\right] = 0$ for $\ell > i$ or $\ell = 0$. Then for all $i \ge 1$:

$$\mathbb{E}[D_{\ell,i}] = \left[{i \atop \ell}\right]\frac{2^\ell}{i!}, \qquad 1 \le \ell \le i,$$

$$\mathbb{E}[B_{k,i}] = \sum_{\ell=0}^{i} \left[{i \atop \ell}\right]\frac{2^\ell}{i!}\, \frac{e^{-\ell\mu}(\ell\mu)^k}{k!}, \qquad k \ge 0.$$

In particular the expected MBD is the expected DD with each division class $\ell$ replaced by a $\mathrm{Pois}(\ell\mu)$ mass function, so it depends on the per-division mutation law only through its mean $\mu$.

## Proof sketch

A cell with division count $\ell$ is picked with probability $D_{\ell,i}/(i+1)$ and replaced by two cells of count $\ell + 1$, so

$$\mathbb{E}[D_{\ell,i+1}] = \Big(1 - \tfrac{1}{i+1}\Big)\mathbb{E}[D_{\ell,i}] + \tfrac{2}{i+1}\mathbb{E}[D_{\ell-1,i}],$$

which the Stirling recursion solves; summing uses $\sum_\ell \left[{i \atop \ell}\right] x^\ell = x(x+1)\cdots(x+i-1)$, giving $\sum_\ell \mathbb{E}[D_{\ell,i}] = (i+1)!/i! = i+1$. A cell with $\ell$ past divisions carries a sum of $\ell$ independent $\mathrm{Pois}(\mu)$ variables, i.e. a $\mathrm{Pois}(\ell\mu)$ burden independent of the tree shape; conditioning on the DD and using linearity gives the MBD formula. The shape of the MBD is therefore driven by lineage-level (tree) stochasticity rather than the per-division mutation distribution. With death probability $\delta = 1 - \beta > 0$, the same conversion applied to the first-order DD approximation $\mathbb{E}[D_{\ell,i}] \simeq \mathbb{E}[N_i]\, f(i,\ell)/\sum_{\ell'} f(i,\ell')$, $f(i,\ell) = \left[{i \atop \ell}\right]2^\ell(1-\delta/\beta)^{-\ell}$ (Proposition S5), gives the birth–death MBD.

## Sources

- Christo Morison, Dudley Stark and Weini Huang, "Single-cell mutational burden distributions in birth–death processes", *PLOS Computational Biology* 21 (2025), e1013241, <https://doi.org/10.1371/journal.pcbi.1013241>. Preprint version: arXiv:2309.06355 (2023), Results (division distribution and mutational burden distribution) and Supplementary Proposition S5, <https://doi.org/10.48550/arXiv.2309.06355>.
