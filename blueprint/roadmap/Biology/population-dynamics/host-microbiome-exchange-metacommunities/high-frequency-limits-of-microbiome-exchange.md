# High-frequency limits of microbiome exchange

**Model.** Hosts $h^{(1)},\dots,h^{(|H|)}$ sit on a weighted network with interaction-frequency parameters $\lambda_{ij}\ge0$; write $\lambda_{\rm tot}=\sum_{i<j}\lambda_{ij}$ and $l_{ij}=\lambda_{ij}/\lambda_{\rm tot}$. Host $i$ carries a microbiome abundance vector $N^{(i)}(t)\in[0,M]^n$. Between interactions, $\dot N^{(i)}=g^{(i)}(N^{(i)})$, where each local-dynamics function $g^{(i)}$ keeps $[0,M]^n$ invariant. Each pair $(i,j)$ interacts at the event times of an independent Poisson process of rate $\lambda_{ij}$, and at an interaction time $t_I$ the two hosts exchange a fraction $\gamma\in(0,1]$ of their microbiomes:

$$N^{(i)}(t_I^+)=(1-\gamma)N^{(i)}(t_I^-)+\gamma N^{(j)}(t_I^-),\qquad N^{(j)}(t_I^+)=(1-\gamma)N^{(j)}(t_I^-)+\gamma N^{(i)}(t_I^-).$$

The result is a piecewise-deterministic Markov process.

**Theorem (high frequency, low strength).** Fix the $l_{ij}$, the product $\lambda_{\rm tot}\gamma$, and $T>0$, and let each $g^{(i)}$ be $C^1$ and bounded. For every $\varepsilon\in(0,1]$ and $\delta>0$, if $\lambda_{\rm tot}$ is large enough then with probability greater than $1-\varepsilon$, $\sup_{[0,T]}\|N^{(i)}-\widetilde N^{(i)}\|_\infty<\delta$ for every host, where

$$\frac{d\widetilde N^{(i)}}{dt}=g^{(i)}(\widetilde N^{(i)})+\sum_j\lambda_{ij}\gamma\,\big(\widetilde N^{(j)}-\widetilde N^{(i)}\big),\qquad \widetilde N^{(i)}(0)=N^{(i)}(0).$$

**Theorem (high frequency, constant strength).** Fix the $l_{ij}$, $\gamma>0$ and $T>0$, with each $g^{(i)}$ Lipschitz and bounded. For every $\varepsilon\in(0,1]$, $\delta>0$ and $\eta>0$, if $\lambda_{\rm tot}$ is large enough then with probability greater than $1-\varepsilon$, $\sup_{[\eta,T]}\|N^{(i)}-\widetilde N\|_\infty<\delta$ for every host, where $\widetilde N$ solves the mean-field equation

$$\frac{d\widetilde N}{dt}=\frac{1}{|H|}\sum_{j=1}^{|H|}g^{(j)}(\widetilde N),\qquad \widetilde N(0)=\frac1{|H|}\sum_jN^{(j)}(0).$$

## Expansion

Each exchange preserves the pair's sum and contracts their difference by the factor $1-2\gamma$. With many weak exchanges ($\gamma\to0$, $\lambda_{\rm tot}\gamma$ fixed) the expected increment of $N^{(i)}$ per unit time is $\sum_j\lambda_{ij}\gamma(N^{(j)}-N^{(i)})$, and the law of large numbers for the Poisson interaction counts turns the jump process into the deterministic diffusively coupled system: the classical dispersal metacommunity with network Laplacian coupling. With many exchanges of fixed strength, the hosts (on a connected network) homogenize within a time of order $1/\lambda_{\rm tot}$ (hence the initial layer $[0,\eta]$), the mean abundance is conserved by exchanges, and the common state then evolves under the host-averaged local dynamics.

## Sources

- Michael Johnson, Mason A. Porter, "Interacting Hosts with Microbiome Exchange: An Extension of Metacommunity Theory for Discrete Interactions between Hosts", arXiv:2507.11958 (2025), Theorems 4.1 and 4.2 (Section 4; proofs in Appendices B and C), <https://doi.org/10.48550/arXiv.2507.11958>
