# Optimal nested pooling strategies use pool-size ratios of three

**Setting.** Individuals are infected independently with prevalence $p \in (0,1)$; write $q = 1-p$. A pooled test on a set of individuals is negative iff all of them are uninfected. A *nested strategy* $(k, \mathbf{m})$ with $\mathbf{m} = (m_1,\ldots,m_k)$, $m_1 > \cdots > m_k$ and each $m_{j+1}$ dividing $m_j$, tests a pool of $m_1$ individuals; if positive, it tests its $m_1/m_2$ sub-pools of size $m_2$; every positive pool of size $m_j$ is split into $m_j/m_{j+1}$ pools of size $m_{j+1}$; finally every member of a positive pool of size $m_k$ is tested individually ($k=0$ means individual testing, cost $1$).

**Proposition (cost).** The expected number of tests per individual is

$$D_k(\mathbf{m},p) = \frac{1}{m_1} + 1 - q^{m_k} + \sum_{j=2}^{k}\frac{1}{m_j}\big(1 - q^{m_{j-1}}\big) = 1 + \sum_{i=1}^{k}\Big(\frac{1}{m_i} - \frac{q^{m_i}}{m_{i+1}}\Big)\quad(m_{k+1} := 1).$$

**Theorem (optimal strategies).** If $p \ge 1 - 3^{-1/3}$, individual testing is optimal. If $p \le 1 - 3^{-1/3}$, some optimal strategy has multipliers $\pi = (m_k, m_{k-1}/m_k, \ldots, m_1/m_2)$ of the form

$$\pi = (2\text{ or }3,\ 3, \ldots, 3,\ 3\text{ or }4),$$

that is $\mathbf{m}$ is one of $(3^k,\ldots,9,3)$, $(4\cdot 3^{k-1}, 3^{k-1},\ldots,3)$, $(2\cdot 3^{k-1},\ldots,6,2)$ or $(8\cdot 3^{k-2}, 2\cdot 3^{k-2},\ldots,6,2)$ for a suitable depth $k = k(p)$; for $(3,\ldots,3)$ the depth is $k_3(p) = \lfloor \log_3(1/|\log_3 q|) + c\rfloor$ with an explicit constant $c$.

**Theorem (cost asymptotics).** For $p \le 1 - 3^{-1/3}$, the powers-of-three strategy satisfies $D_{k_3}(\mathbf{m}_{33}, p) \le \frac{3}{\log 3}\, p\log(1/p) + 6p$, the optimal cost is $D_{\mathrm{opt}}(p) = O(p\log(1/p))$, and

$$\big|D_{k_3}(\mathbf{m}_{33},p) - D_{\mathrm{opt}}(p)\big| \le \Big(\frac{3}{\log 3} - e\Big)p\log(1/p) + 12p + 4p^2\log(1/p),$$

where $\frac{3}{\log 3} - e \approx 0.013$.

## Expansion

The cost formula follows because a pool of size $m_j$ ($j \ge 2$) is tested only if its parent pool of size $m_{j-1}$ is positive, and $(1-Y_{\text{parent}})(1-Y_{\text{child}}) = 1-Y_{\text{child}}$. Optimality is proved by a sequence of local exchange lemmas on the multipliers showing that an optimal strategy can only use the multipliers listed; heuristically, each stage trades a factor-$\pi$ split against one extra test, and the integer maximizing $\pi^{1/\pi}$ is $3$ (the same reason $3$ is the most economical radix). Summing the per-stage costs of the powers-of-three strategy gives the leading term $\frac{3}{\log 3}\,p\log(1/p)$, and the comparison bound shows no nested strategy improves the constant by more than $\frac{3}{\log 3} - e$.

## Sources

- Inés Armendáriz, Pablo A. Ferrari, Daniel Fraiman, José M. Martínez and Silvina Ponce Dawson, "Group Testing With Nested Pools", IEEE Transactions on Information Theory 68 (2022), 1119–1132, <https://doi.org/10.1109/tit.2021.3123929>; numbering as in arXiv:2005.13650: Proposition 2.1, Theorem 3.1, Propositions 3.1–3.2 and Theorem 5.1.
