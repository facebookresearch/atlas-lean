# VSTAT oracle and statistical dimension with average correlation

For a distribution $D$ on a domain $\mathcal{X}$ and $t > 0$, the oracle **VSTAT($t$)** answers a query $h : \mathcal{X} \to [0,1]$ with any value $v$ such that $|v - p| \le \max\{1/t,\, \sqrt{p(1-p)/t}\}$, where $p = \mathbb{E}_D[h]$; it mimics the accuracy of an empirical average over $t$ samples. For a reference distribution $D$ and distributions $D_1, D_2$, the **pairwise correlation** is $\chi_D(D_1, D_2) = \mathbb{E}_D\big[(\tfrac{dD_1}{dD} - 1)(\tfrac{dD_2}{dD} - 1)\big]$. A decision problem (distinguish $D$ from a family $\mathcal{D}$) has **statistical dimension** at least $d$ with average correlation $\gamma$, written $\mathrm{SDA}(\mathcal{D}, \gamma) \ge d$, if every subfamily $\mathcal{D}' \subseteq \mathcal{D}$ of size at least $|\mathcal{D}|/d$ has average pairwise correlation $\frac{1}{|\mathcal{D}'|^2}\sum_{D_1, D_2 \in \mathcal{D}'} |\chi_D(D_1, D_2)| \le \gamma$.

## Sources

- V. Feldman, E. Grigorescu, L. Reyzin, S. Vempala, Y. Xiao, "Statistical Algorithms and a Lower Bound for Detecting Planted Cliques", Journal of the ACM 64 (2017), arXiv:1201.1214.
