# Re-infection-time estimator of high-degree vertices in SIS epidemics

**Model.** A stochastic SIS epidemic runs on an unknown graph $G$ with vertex set $V$, $|V|=n$, with unknown infection rate $\beta>0$ and recovery rate $\gamma>0$ (both fixed as $n\to\infty$): an infected vertex recovers at rate $\gamma$, and a susceptible vertex $v$ becomes infected at rate $\beta\,|\mathcal N(v)\cap\mathcal I(t)|$, where $\mathcal I(t)$ is the set of infected vertices. The initial configuration is arbitrary. The observer sees only the infection and recovery times of every vertex during $[0,T]$.

Assume there are at most $m$ vertices of degree at least $D=n^{\alpha}$, $\alpha\in(0,1)$, while every other vertex has degree at most $d$, with $m$ constant and $d=n^{o(1)}$ as $n\to\infty$.

**Estimator.** For a vertex $v$ let $I_k(v)$ be its $k$-th infection time and $S_k(v)$ its $k$-th recovery time after infection. For a re-infection number $K$ and threshold $h>0$, among vertices infected more than $K$ times in $[0,T]$ compute
$$R_K(v)=\max_{1\le k\le K}\big(I_{k+1}(v)-S_k(v)\big)$$
and output $\widehat{\mathrm{HD}}=\{v:R_K(v)\le h\}$. Take $h=n^{-\alpha/2}$.

**Theorem.**
1. Let $V_K(T)$ be the set of vertices infected more than $K$ times in $[0,T]$. If $K>2/\alpha$, then with probability $1-o(1)$,
$$\widehat{\mathrm{HD}}=\{v\in V_K(T):\deg(v)\ge n^{\alpha}\}.$$
2. Let $\delta>0$, $K=\lceil3/\alpha\rceil$, and let $v$ have $\deg(v)\ge n^\alpha$ and be infected during $[0,1]$. If $T=\Omega\big(\alpha^{-1}\log(1/\delta)\big)$, then $\mathbb P(v\in\widehat{\mathrm{HD}})\ge1-\delta$.

So super-spreaders can be identified after a constant observation time (independent of $n$), whereas full network reconstruction needs time growing with $n$. Vaccinating $\widehat{\mathrm{HD}}$ then approximates degree-targeted immunisation without knowing the graph.

## Expansion

A low-degree vertex has at most $d$ neighbours, so each re-infection gap $I_{k+1}(v)-S_k(v)$ stochastically dominates an independent $\mathrm{Exp}(d\beta)$ variable. Hence all $K$ gaps are at most $n^{-\alpha/2}$ with probability at most $(d\beta\,n^{-\alpha/2})^K=n^{-K\alpha/2+o(1)}=o(1/n)$ when $K>2/\alpha$, and a union bound over the $n$ vertices excludes every low-degree vertex. For a vertex with $\deg(v)\ge n^\alpha$, the recovery time of $v$ is of order one, so at its recovery at least $n^{\alpha-o(1)}$ neighbours are infected (each neighbour is infected by $v$ and still infected with probability $n^{-o(1)}$, and Hoeffding's inequality concentrates the count). Each such neighbour infects $v$ before recovering with probability $\beta/(\beta+\gamma)$, so at least $n^{\alpha-\varepsilon}$ of them stay infected until $v$ is re-infected, and the re-infection gap is dominated by an $\mathrm{Exp}(n^{\alpha-\varepsilon})$ variable: $I_2(v)-S_1(v)\le n^{-\alpha+o(1)}$ with probability $1-o(1)$. The strong Markov property at successive infection times and a union bound over $k\le K$ give $R_K(v)\le n^{-\alpha+o(1)}<h$. For the time horizon, each infection–recovery–re-infection cycle of a high-degree vertex takes $O(1)$ time, so $K=O(1/\alpha)$ cycles fit in time $O(\alpha^{-1}\log(1/\delta))$ with probability $1-\delta$.

## Sources

- Anirudh Sridhar and Arnob Ghosh, "Finding Super-spreaders in SIS Epidemics", arXiv:2602.12568 (2026), Section 2.1 (model and degree assumption), Section 2.2 (the two main theorems and the remark on epidemic control) and Section 2.3 (estimation algorithm); proofs in Section 3. <https://doi.org/10.48550/arXiv.2602.12568>
