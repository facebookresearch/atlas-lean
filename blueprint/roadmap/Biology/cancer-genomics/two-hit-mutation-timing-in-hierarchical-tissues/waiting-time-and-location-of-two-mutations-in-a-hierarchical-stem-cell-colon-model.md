# Waiting time and location of two mutations in a hierarchical stem-cell colon model

**Model (Komarova's hierarchical crypt).** Fix $N=2^l$. The tissue is a stem cell plus $l$ generations of daughter cells, generation $i$ holding $2^{i-1}$ cells. At each integer time the stem cell divides into a stem cell and a generation-1 daughter, every generation-$i$ daughter becomes two generation-$(i+1)$ daughters, and the last generation is shed. Type-1 and then type-2 (cancer) mutations arrive as Poisson processes at rates $u_1,u_2$ on the stem lineage and $v_1,v_2$ on daughters, with $u_1\le u_2$, $v_1\le v_2$, all tending to $0$ as $N\to\infty$, and $N^{-\alpha-\epsilon}\ll v_2\ll N^{-\alpha+\epsilon}$ for some $\alpha>0$ and all $\epsilon>0$. Let $\tau$ be the first time some cell carries a type-2 mutation, and $\sigma,\rho\in[0,1]$ the depths (generation$/l$, stem cell $=0$) of the cancer-causing type-1 and of the first type-2 mutation. Logarithms are base $2$.

**Theorem.** Let $X\sim\mathrm{Exp}(1)$ and $Y$ Rayleigh, $\mathbb{P}(Y\le t)=1-e^{-t^2/2}$. As $N\to\infty$:
1. If $v_1v_2\ll 1/(N(\log N)^2)$ and $v_1v_2N\log N\gg u_1$, then $(\alpha\wedge1)\,v_1v_2N\log N\,\tau\Rightarrow X$; $\sigma$ converges in law to the uniform distribution on $((1-\alpha)^+,1]$ and $\rho\to1$ in probability.
2. If $1/(N(\log N)^2)\ll v_1v_2\ll 1/N$ and $\sqrt{v_1v_2N}\gg u_1$, then $\sqrt{v_1v_2N}\,\tau\Rightarrow Y$, and $\sigma,\rho\to 1$.
3. If $v_1v_2\gg 1/N$, then $\sqrt{v_1v_2N}\,\tau\Rightarrow Y$, and $\sigma,\rho\to1$.
4. If $u_1$ dominates the daughter pathway ($u_1\gg v_1v_2N\log N$ in the first regime, or $u_1\gg\sqrt{v_1v_2N}$ in the second) and $u_2\ll 1/\log N$, $u_2\ll Nv_2$, then $u_1\tau\Rightarrow X$, the first mutation hits the stem cell with probability $\to1$, and $\rho\to\alpha\wedge1$.
5. Under the same $u_1$-dominance but $u_2\gg1/\log N$ or $u_2\gg Nv_2$: if $u_1\ll u_2$ then $u_1\tau\Rightarrow X$; if $u_1\sim Au_2$ with $A\ge1$ then $u_1\tau\Rightarrow X+Z$ with $Z\sim\mathrm{Exp}(1/A)$ independent; both mutations occur on the stem cell with probability $\to1$.

## Expansion

A daughter type-1 mutation in generation $i$ is *successful* if one of its $2^{l-i+1}-2$ descendants acquires a type-2 mutation before being shed, so the effective rate of successful daughter first hits is $\sum_i v_12^{i-1}\big(1-e^{-v_2(2^{l-i+1}-2)}\big)$. When $v_2$ is tiny, only mutations high in the hierarchy (with many descendants) succeed, each with probability about $v_2\cdot 2^{l-i}$, and the $\log N$ generations contribute equally, giving an exponential waiting time at rate of order $v_1v_2N\log N$. When $v_1v_2N$ is larger, the second hit typically comes within one wave of a single clone, and the time to the first success, a sum of increasing hazards, has a Rayleigh limit. If the stem cell is mutated first, the mutation fixes in the crypt in $l$ steps and the second hit then follows on the stem lineage or among its daughters.

## Sources

- Michael Kelly, "A Hierarchical Probability Model of Colon Cancer", arXiv:1005.3451 (2010), model and notation in Section 1 and Theorem 1 (main theorem), <https://doi.org/10.48550/arXiv.1005.3451>.
