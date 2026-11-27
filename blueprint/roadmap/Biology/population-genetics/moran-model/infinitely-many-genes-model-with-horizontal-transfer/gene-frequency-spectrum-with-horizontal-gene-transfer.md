# Gene frequency spectrum of the infinitely many genes model with horizontal transfer

**Model.** A Moran model of $N$ haploid bacteria in which each individual carries a finite set of accessory genes drawn from an infinite pool. Each pair of individuals resamples at rate $1$. Each individual gains a brand-new gene at rate $\theta/2$, each gene in each individual is lost at rate $\rho/2$, and for each ordered pair $(i,j)$ every gene of $i$ is transferred to $j$ (horizontal gene transfer) at rate $\gamma/(2N)$. In a sample of $n$ individuals from the equilibrium, let $G_k^{(n)}$ be the number of genes present in exactly $k$ sampled individuals (the gene frequency spectrum), $A^{(n)}$ the average number of accessory genes per individual, $D^{(n)}$ the average number of genes present in one individual but not in another, and $G^{(n)} = \sum_{k\ge1}G^{(n)}_k$ the size of the sample's accessory genome (pangenome minus core). Write $(a)_{m\uparrow} = a(a+1)\cdots(a+m-1)$ and $(a)_{m\downarrow} = a(a-1)\cdots(a-m+1)$.

**Theorem.** In the large-population limit, with $\rho > 0$, $\theta > 0$, $\gamma \ge 0$:

1. The frequency $X$ of a single gene converges to the diffusion

$$dX = \Bigl(-\tfrac\rho2 X + \tfrac\gamma2 X(1-X)\Bigr)dt + \sqrt{X(1-X)}\,dW .$$

So horizontal transfer acts exactly like positive selection of strength $\gamma$.

2. (Gene frequency spectrum.)

$$\mathbb E\bigl[G_k^{(n)}\bigr] = \frac\theta k\,\frac{(n)_{k\downarrow}}{(n-1+\rho)_{k\downarrow}}\Bigl(1 + \sum_{m=1}^\infty\frac{(k)_{m\uparrow}\,\gamma^m}{(n+\rho)_{m\uparrow}\,m!}\Bigr), \qquad k = 1,\dots,n.$$

3. (Summary statistics.)

$$\mathbb E[A^{(n)}] = \frac\theta\rho\Bigl(1 + \sum_{m\ge1}\frac{\gamma^m}{(1+\rho)_{m\uparrow}}\Bigr), \qquad \mathbb E[D^{(n)}] = \frac{\theta}{1+\rho}\Bigl(1 + \sum_{m\ge1}\frac{\gamma^m}{(2+\rho)_{m\uparrow}}\Bigr),$$

$$\mathbb E[G^{(n)}] = \theta\sum_{k=0}^{n-1}\frac{1}{k+\rho} + \theta\sum_{m\ge1}\frac{\gamma^m}{m}\Bigl(\frac{1}{(\rho)_{m\uparrow}} - \frac{1}{(n+\rho)_{m\uparrow}}\Bigr).$$

For $\gamma = 0$ these reduce to the infinitely-many-genes formulas without transfer, $\mathbb E[G_k^{(n)}] = \frac\theta k\frac{(n)_{k\downarrow}}{(n-1+\rho)_{k\downarrow}}$. Transfer inflates the high-frequency classes most, producing the U-shaped gene frequency spectra seen in bacterial pangenomes. As $\gamma \to 0$, the variances of $A^{(1)}$ and $D^{(2)}$ are known to orders $\gamma^2$ and $\gamma$ respectively.

## Expansion

Genes arise as a Poisson stream of rate $\theta/2$ per lineage, so $\mathbb E[G_k^{(n)}] = \binom nk\int_0^1\theta\, x^k(1-x)^{n-k}\,\pi(dx)$, where $\pi$ is the Green (occupation) density of the frequency diffusion started near $0$. The speed and scale densities give $\pi(dx) \propto x^{-1}(1-x)^{\rho-1}e^{\gamma x}dx$, and expanding $e^{\gamma x}$ in powers of $\gamma$ and integrating Beta functions gives the series. Genealogically, a gene sampled in $k$ individuals is traced back through the ancestral gene transfer graph: a Kingman coalescent in which lines are lost at rate $\rho/2$ (gene loss) and split at rate $\gamma/2$ (transfer from an outside donor). The $m$-th term of the series counts histories with $m$ transfer events.

## Sources

- Franz Baumdicker, Peter Pfaffelhuber, "The infinitely many genes model with horizontal gene transfer", *Electronic Journal of Probability* 19 (2014), <https://doi.org/10.1214/EJP.v19-2642>; preprint arXiv:1301.6547, <https://doi.org/10.48550/arXiv.1301.6547>. Numbering of the arXiv version: Section 2 (Definition 2.1, Lemma 2.5), Section 3 (Theorems 1–3), Section 5 (ancestral gene transfer graph, Definitions 5.1 and 5.4).
