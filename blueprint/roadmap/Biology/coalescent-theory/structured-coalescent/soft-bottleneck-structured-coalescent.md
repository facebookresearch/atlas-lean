# Structured coalescent with soft bottlenecks

Consider a haploid Wright-Fisher population on $D$ islands (demes) of sizes $\omega_iN$, $\omega_i>0$, $\sum_i\omega_i=1$. Each generation, reproduction is Wright-Fisher within each deme and then a fixed number $c_{ij}$ of individuals migrates from deme $i$ to deme $j$, with $\sum_{j\ne i}c_{ij}=\sum_{j\ne i}c_{ji}$. Recurrent **soft bottlenecks** hit one uniformly chosen deme at a time: the gaps between bottlenecks are i.i.d. geometric with parameter $\gamma/N$; the $k$-th bottleneck lasts $l_k^N$ generations with $l_k^N\to\infty$ and $l_k^N/N\to 0$; and during it the size of the affected deme is $R_k(\lfloor l_k^Nt\rfloor)$ with $R_k(\lfloor l_k^Nt\rfloor)/l_k^N\to\varphi(t)$ for a continuous $\varphi:[0,1]\to(0,\infty)$. The **effective length** of a bottleneck is $\Lambda=\int_0^1\varphi(t)^{-1}dt$.

For a sample of $n$ genes let $\Pi^N(g)$ be the ancestral process on marked partitions of $[n]$ (blocks = lineages with a common ancestor, marks = deme of that ancestor $g$ generations back). For deme $i$ let $\Pi^{(i)}$ be the process in which any two $i$-blocks merge at rate $1$ and any $i$-block is relabelled as a $j$-block at rate $c_{ji}$, with all other blocks frozen. Define the **soft-bottleneck structured coalescent** $\Pi$ by the rates

- $\frac{1}{\omega_i}+\frac{\gamma}{D}\,\mathbb P_\xi(\Pi^{(i)}(\Lambda)=\eta)$ for a merger of two $i$-blocks,
- $\frac{c_{ji}}{\omega_i}+\frac{\gamma}{D}\,\mathbb P_\xi(\Pi^{(i)}(\Lambda)=\eta)$ for a single migration of an $i$-block to deme $j$,
- $\frac{\gamma}{D}\,\mathbb P_\xi(\Pi^{(i)}(\Lambda)=\eta)$ for any other transition $\xi\to\eta$ involving only mergers and relabellings of $i$-blocks.

**Theorem.** If $\Pi^N(0)\Rightarrow\Pi(0)$, then $(\Pi^N(\lfloor Nt\rfloor))_{0\le t\le T}$ converges weakly to $(\Pi(t))_{0\le t\le T}$ for every $T>0$. The limit is a multi-type coalescent with simultaneous multiple mergers and migrations, and its block-counting process is moment dual to the limiting allele-frequency process: $\mathbb E_x\big[\prod_iX_i(t)^{n_i}\big]=\mathbb E_n\big[\prod_ix_i^{N_i(t)}\big]$, where $X$ is a structured Wright-Fisher diffusion with migration drift $\sum_{j\ne i}\frac{c_{ji}}{\omega_i}(x_j-x_i)$, noise $\frac{1}{\omega_i}x_i(1-x_i)$, and jumps at rate $\gamma/D$ that replace $x_i$ by the value at time $\Lambda$ of the single-deme bottleneck diffusion started from $x$.

## Expansion

On the time scale of $N$ generations a bottleneck is instantaneous. During it the affected deme has size of order $l_k^N$ and lasts $l_k^N$ generations, so its lineages follow a Kingman coalescent with emigration run for $\int_0^1\varphi(t)^{-1}dt=\Lambda$ units of its own time, while the other demes are unchanged; the outcome is a single multiple-merger-and-migration jump. Shorter bottlenecks would leave only a time-rescaled structured Kingman coalescent, and longer ones would empty the affected deme of lineages. Between bottlenecks the usual structured Kingman coalescent with migration runs.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Sources

- Marta Dai Pra, Alison Etheridge, Jere Koskela, Maite Wilke-Berenguer, "Multi-type Xi-coalescents from structured population models with bottlenecks", arXiv:2504.11875 (2025), Theorems 3, 4 and 5, <https://doi.org/10.48550/arXiv.2504.11875>
