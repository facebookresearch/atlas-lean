# Accessory-genome summary statistics under horizontal gene transfer

In the infinitely-many-genes model with gene gain rate $\theta > 0$, loss rate $\rho > 0$ and horizontal transfer rate $\gamma \ge 0$ (see the [gene frequency spectrum](gene-frequency-spectrum-under-horizontal-gene-transfer.md)), sample $n$ cells with accessory genomes $\mathcal G_1,\dots,\mathcal G_n$ from the equilibrium population and define

- the average number of accessory genes $A^{(n)} = \frac1n \sum_{i=1}^{n} |\mathcal G_i|$,
- the average number of pairwise differences $D^{(n)} = \frac{1}{n(n-1)} \sum_{i \neq j} |\mathcal G_i \setminus \mathcal G_j|$,
- the size of the sampled accessory genome (pangenome) $G^{(n)} = |\mathcal G_1 \cup \dots \cup \mathcal G_n|$.

**Corollary (Baumdicker–Pfaffelhuber, Corollary 2).** As $N \to \infty$,

$$E\big[A^{(n)}\big] = \frac{\theta}{\rho}\Big(1 + \sum_{m=1}^{\infty} \frac{\gamma^m}{(1+\rho)_m}\Big), \qquad E\big[D^{(n)}\big] = \frac{\theta}{1+\rho}\Big(1 + \sum_{m=1}^{\infty} \frac{\gamma^m}{(2+\rho)_m}\Big),$$

$$E\big[G^{(n)}\big] = \theta \sum_{k=0}^{n-1} \frac{1}{k+\rho} + \theta \sum_{m=1}^{\infty} \frac{\gamma^m}{m} \Big( \frac{1}{(\rho)_m} - \frac{1}{(n+\rho)_m} \Big),$$

with $(a)_b = a(a+1)\cdots(a+b-1)$. At $\gamma = 0$ these reduce to $\theta/\rho$, $\theta/(1+\rho)$ and $\theta\sum_{k=0}^{n-1} 1/(k+\rho)$, the values without transfer. The transfer term in $E[G^{(n)}]$ stays bounded as $n \to \infty$.

## Depends on

- [Gene frequency spectrum under horizontal gene transfer](gene-frequency-spectrum-under-horizontal-gene-transfer.md)

## Expansion

All three statistics are functionals of gene frequency spectra of smaller samples: $E[A] = E[G^{(1)}_1]$ and $E[D] = E[G^{(2)}_1]$ by exchangeability, and by exchangeability the expected number of genes carried by the $k$-th sampled cell but by none of the first $k-1$ equals $\frac1k E[G^{(k)}_1]$, so $E[G] = \sum_{k=1}^{n} \frac1k E[G^{(k)}_1]$. Substituting $E[G^{(k)}_1] = \frac{\theta k}{k-1+\rho}\sum_{m\ge0} \frac{\gamma^m}{(k+\rho)_m}$ and telescoping

$$\frac{1}{(k+\rho)_{m+1}} = \frac{1}{m}\Big(\frac{1}{(k+\rho)_m} - \frac{1}{(k+1+\rho)_m}\Big)$$

over $k$ gives the closed form for $E[G^{(n)}]$.

## Sources

- F. Baumdicker and P. Pfaffelhuber, *Evolution of bacterial genomes under horizontal gene transfer*, arXiv:1105.5014 (2011). <https://doi.org/10.48550/arXiv.1105.5014>
