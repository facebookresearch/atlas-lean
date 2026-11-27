# Large-sample asymptotics of branch lengths in birth–death genealogies

**Setting.** Start a birth–death process from one individual; each individual gives birth at rate $\lambda$ and dies at rate $\mu$, net growth rate $r=\lambda-\mu\ge0$, and $N_t$ is the population size. At time $T$, conditionally on $N_T\ge n$, sample $n$ individuals uniformly and form their genealogical tree. Let $L^k_{n,T}$ be the total length of branches supporting exactly $k$ sampled leaves. Under neutral mutations at rate $\nu$ per unit branch length (infinitely many sites), the site frequency spectrum count $M^k_{n,T}$ of mutations carried by exactly $k$ sampled individuals is, given the tree, Poisson with mean $\nu L^k_{n,T}$, so the SFS is governed by the $L^k_{n,T}$. The genealogy can be generated exactly as a *coalescent point process*: i.i.d. node depths $H_{i,n,T}$ with explicit law.

**Theorem (critical case).** Let $\lambda=\mu=1$, $K\ge1$ fixed, and $T_n$ with $n/T_n\to0$. Then

$$\sqrt{\frac n{\log n}}\Big(\frac{L^k_{n,T_n}}{N_{T_n}}-\frac1k\Big)_{k=1}^K\ \Rightarrow\ N(0,I_{K\times K}).$$

**Theorem (supercritical case).** Allow $\lambda=\lambda_n$, $\mu=\mu_n$, $T=T_n$, $r_n=\lambda_n-\mu_n>0$, and fix $k\ge2$.
1. If $ne^{-r_nT_n}\to0$, then $\dfrac{r_n}{n}L^k_{n,T_n}\xrightarrow{P}\dfrac1{k(k-1)}$.
2. If $n^{3/2}(\log n)e^{-r_nT_n}\to0$, then for fixed $K\ge2$,

$$\Big(\frac{r_n}{\sqrt n}\Big(L^k_{n,T_n}-\frac{n}{r_nk(k-1)}\Big)\Big)_{k=2}^K\Rightarrow N(0,V),$$

with an explicit covariance matrix $V$; for instance $V_{k,k}=\frac{2}{(k-1)^2(2k-1)}-\frac{2k+1}{k^2(k-1)^2}-\frac2{k-1}+\frac{\pi^2}3-2\sum_{j=1}^{k-2}j^{-2}$.

## Expansion

In the coalescent point process the sampled leaves are placed on a line and consecutive leaves are separated by independent node depths $H_i$; the branch above leaf $i$ supports $k$ leaves over a stretch determined by maxima of $k-1$ consecutive depths, so $L^k$ is a sum of weakly dependent terms over $i$. For supercritical growth the depths, rescaled by $r_n$, are approximately logistic (the tree looks like a Yule tree in log time), each consecutive block contributes on average $1/(r_nk(k-1))$, and summing $n$ nearly independent terms gives the law of large numbers and a $\sqrt n$ central limit theorem, sharpening Durrett's $\lim_T\mathbb E[L^k_{n,T}]=n/(rk(k-1))$ for exponentially growing populations. In the critical case the depths are heavy-tailed, which produces the $1/k$ profile of branch length per individual and the $\log n$ normalization, paralleling the Dahmer–Kersting results for internal branch lengths of Kingman's coalescent. The $1/(k(k-1))$ profile is the classical signature used to detect neutral exponential growth in tumour sequencing data.

## Sources

- Jason Schweinsberg and Yubo Shuai, "Asymptotics for the site frequency spectrum associated with the genealogy of a birth and death process", Ann. Appl. Probab. 35 (2025), 99–141, <https://doi.org/10.1214/24-AAP2110>. Numbering follows the arXiv version, arXiv:2304.13851 (2023): Theorems 1.1, 1.3 and 1.4 and Section 2 (coalescent point process), <https://doi.org/10.48550/arXiv.2304.13851>.
