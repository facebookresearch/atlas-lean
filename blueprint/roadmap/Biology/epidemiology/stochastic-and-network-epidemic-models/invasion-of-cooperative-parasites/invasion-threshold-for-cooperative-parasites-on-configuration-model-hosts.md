# Invasion threshold for cooperative parasites on a configuration-model host graph

**Model.** $N$ hosts sit on the vertices of a $d_N$-regular configuration-model graph, one host per vertex. One host is initially infected; an infection kills the host and releases $v_N$ offspring parasites. In each discrete generation every free parasite moves to a uniformly chosen neighboring vertex. A host attacked by at least two parasites simultaneously is infected (cooperative infection); a host attacked by a single parasite is infected only with probability $\rho_N$. Each infection kills the host and the attacking parasites and produces $v_N$ new parasites; parasites landing on empty vertices keep moving. Let $\bar I_n^{(N)}$ be the number of hosts infected up to generation $n$, and $E_u^{(N)} = \{\exists n : \bar I_n^{(N)} \ge uN\}$ the event of invasion of a fraction $u \in (0,1]$.

**Theorem.** Assume $d_N = \Theta(N^\beta)$ for some $0 < \beta < 1$ and $\rho_N v_N \to x \in [0,1]$.
1. If $v_N = o(\sqrt{d_N})$, then $\mathbb{P}(E_u^{(N)}) \to 0$ for every $u \in (0,1]$.
2. If $v_N \sim c\sqrt{d_N}$ with $c > 0$, then for every $u \in (0,1]$

$$\lim_{N\to\infty}\mathbb{P}(E_u^{(N)}) = \pi(c,x),$$

the survival probability of a Galton–Watson process with $\mathrm{Poisson}(c^2/2 + x)$ offspring; in particular invasion fails with high probability when $c^2/2 + x \le 1$.
3. If $\sqrt{d_N} = o(v_N)$, then $\mathbb{P}(E_1^{(N)}) \to 1$: all hosts are eventually infected with high probability.

## Expansion

The $v_N$ offspring of an infected host spread over its $d_N$ neighbors, so the number of neighbors hit by two parasites is approximately $\mathrm{Poisson}\big(\binom{v_N}{2}/d_N\big) \approx \mathrm{Poisson}(c^2/2)$ when $v_N \approx c\sqrt{d_N}$, while single hits succeed with mean about $v_N\rho_N \to x$. Early on the graph is locally tree-like and few hosts are depleted, so the infected-host process is sandwiched between Galton–Watson processes with offspring mean close to $c^2/2 + x$; this identifies the critical spatial scale $v_N \asymp \sqrt{d_N}$ at which cooperation turns invasion from unlikely to likely. Once a polynomial number of hosts are infected, the parasite cloud is dense enough that pair hits are ubiquitous and the epidemic sweeps the graph. The model is motivated by phages that need to co-infect a bacterium to overcome CRISPR-based defence.

## Sources

- Vianney Brouard and Cornelia Pokalyuk, "Invasion of cooperative parasites in moderately structured host populations", Stochastic Processes and their Applications 153 (2022), 221–263, <https://doi.org/10.1016/j.spa.2022.06.024>; numbering as in arXiv:2201.02249: Definition 2.1 and Theorem 2.2 (Section 2), Propositions 3.3, 4.1 and 5.1.
