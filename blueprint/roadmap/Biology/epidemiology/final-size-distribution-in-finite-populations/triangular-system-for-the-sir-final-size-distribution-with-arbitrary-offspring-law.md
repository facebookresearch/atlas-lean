# Triangular system for the SIR final-size distribution with arbitrary offspring law

**Setting.** A susceptible–infected–recovered (SIR) infection is introduced into one individual of a closed population of size $N$. Each infected individual independently makes a random number of transmissions with probability generating function $\mu(x)=\sum_\ell p_\ell x^\ell$; each transmission goes to an individual chosen uniformly from the other $N-1$ (with replacement), and only the first transmission to a susceptible infects. Encoding potential transmissions as a random directed graph on $\{1,\dots,N\}$ with the index case $1$, the outbreak is the out-component of node $1$. Let $q_k$ be the probability that the final size, including the index case, equals $k$.

**Theorem.** For $1\le k\le M\le N$ set

$$c_{k,M}=\Big[\mu\Big(\frac{M-1}{N-1}\Big)\Big]^{-k}\prod_{j=1}^{k-1}\frac{M-j}{N-j}.$$

Then $(q_1,\dots,q_N)$ is the unique solution of the lower-triangular linear system

$$\sum_{k=1}^Mc_{k,M}\,q_k=1,\qquad M=1,2,\dots,N,$$

which is solved by forward substitution. For Poisson offspring with mean $R_0$, $\mu(x)=e^{-R_0(1-x)}$ and with $p=1-e^{-R_0/(N-1)}$ the coefficients become

$$c_{k,M}=(1-p)^{-k(N-M)}\prod_{j=1}^{k-1}\frac{M-j}{N-j},$$

recovering the classical final-size equations (each ordered pair carries an independent potential transmission with probability $p$). The same argument, with an extra source node, handles several independent introductions, and the resulting likelihood of outbreak sizes in many small populations allows inference of $R_0$ and the offspring dispersion, though with identifiability limitations.

## Expansion

Fix $M$ and compute the probability that no potential transmission leaves $\{1,\dots,M\}$ in two ways. Directly, each of the $M$ individuals sends all transmissions inside, with probability $\mu\big((M-1)/(N-1)\big)$, giving $\big[\mu\big(\tfrac{M-1}{N-1}\big)\big]^M$. Alternatively, by a graph lemma, no edge leaves $\{1,\dots,M\}$ iff the out-component of $1$ lies inside it and the remaining $M-k$ nodes of the set send no edge outside. Conditioning on the out-component having size $k$ (probability $q_k$), its other $k-1$ members lie in $\{2,\dots,M\}$ with probability $\binom{M-1}{k-1}/\binom{N-1}{k-1}=\prod_{j<k}\frac{M-j}{N-j}$ by exchangeability, and the other $M-k$ nodes, whose edges are independent of that event, contribute $\big[\mu\big(\tfrac{M-1}{N-1}\big)\big]^{M-k}$. Equating the two expressions and dividing by the left side gives the $M$-th equation; $c_{M,M}>0$ makes the system triangular and invertible.

## Sources

- Joel C. Miller, "Distribution of outbreak sizes for SIR disease in finite populations", arXiv:1907.05138 (2019), Section 3 (Poisson case and equation for $c_{k,M}$), Section 4 (general offspring distributions, single and multiple introductions), Section 6 (inference) and Lemma 1 of the appendix, <https://doi.org/10.48550/arXiv.1907.05138>.
