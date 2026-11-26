# Sufficient observers and Laplace transforms for tree source localization

**Model.** A finite tree $T=(V,E)$ is known. An SI infection starts at time $0$ at an unknown source $s\in V$ and crosses each edge $e$ after an independent delay $\tau_e>0$ with known continuous law and Laplace transform $\varphi_e$. Node $v$ is infected at $\tau_v=\sum_{e\in[s,v]}\tau_e$, where $[u,v]$ is the path from $u$ to $v$. Only the infection times $\tau=(\tau_o)_{o\in\mathcal O}$ of a proper subset $\mathcal O\subset V$ of observers are seen.

**Classes and feasibility.** Non-observers $u,v$ are equivalent if $[u,v]\cap\mathcal O=\emptyset$; let $[\mathcal O]$ be the classes and $\partial r$ the observers adjacent to class $r$. A class $r$ is feasible for a realization $\tau$ if, for every $o\in\partial r$, any observer $o_1$ that is an ancestor of an observer $o_2$ in the subtree hanging from $o$ away from $r$ satisfies $\tau_{o_1}\le\tau_{o_2}$. A set $R$ of classes is a star arrangement if $\bigcap_{r\in R}\partial r\ne\emptyset$.

**Theorem (feasible classes).** Almost surely, the source cannot lie in a non-feasible class, and a class $r$ is feasible iff the first-infected observer $\arg\min_{o\in\mathcal O}\tau_o$ lies in $\partial r$. Hence at least one feasible class exists and the feasible classes form a star arrangement.

**Theorem (sufficient observers).** If $R$ is a star arrangement and $s\in\bigcup_{r\in R}r$, then $(\tau_o)_{o\in\partial R}$ is a sufficient statistic for $s$: the other observers carry no further information about the source.

**Theorem (Laplace transform).** For $v\in V\setminus\mathcal O$ and $t\in[0,\infty)^{\mathcal O}$, with $\mathcal O(e\mid v)=\{o\in\mathcal O:e\in[v,o]\}$,
$$\varphi_v(t):=\mathbb E\big(e^{-\langle t,\tau\rangle}\mid s=v\big)=\prod_{e\in E}\varphi_e\Big(\sum_{o\in\mathcal O(e\mid v)}t_o\Big).$$
The source is identifiable when the laws of $\tau$ under different candidate sources differ, which can be checked by comparing these transforms. Conditioning on one observed time uses $\mathbb E\big(e^{-\sum_ic_i\tau_i}\mid\sum_i\tau_i=t\big)=(\mathcal L_{c_1}f_1*\dots*\mathcal L_{c_k}f_k)(t)/(f_1*\dots*f_k)(t)$ for independent delays with densities $f_i$ and exponentially tilted densities $\mathcal L_cf(x)=e^{-cx}f(x)$.

## Depends on

- [Epidemics on networks](../epidemics-on-networks/README.md)

## Expansion

Given $s=v$, $\langle t,\tau\rangle=\sum_o t_o\sum_{e\in[v,o]}\tau_e=\sum_e\tau_e\sum_{o\in\mathcal O(e\mid v)}t_o$, and independence of the edge delays factors the expectation. Feasibility is a monotonicity check: if the source is in $r$, infection reaches observers outward from $r$, so along each branch an observer is infected before those further out; the earliest observer must border the source's class. Observers further out than $\partial R$ only add independent delays to times already observed, which gives sufficiency.

## Sources

- K. O'Connor, J. M. Jess, D. Costello, M. E. Lladser, "Observer-Based Source Localization in Tree Infection Networks via Laplace Transforms", arXiv:2510.09828 (2025), Section 1.1 (model), Section 2 (feasibility, Theorems 2.2 and 2.3), Theorem 3.1, Theorem 4.2, <https://doi.org/10.48550/arXiv.2510.09828>.
