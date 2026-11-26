# Conditional coalescent given the pedigree in diploid Cannings models

**Model.** A diploid, bi-parental, exchangeable Cannings population has $N$ individuals per generation; offspring numbers $(V_1, \dots, V_N)$ with $\sum_i V_i = 2N$ are exchangeable, and each child's two parents and the parental gene copy it inherits (Mendelian, each with probability $1/2$) are drawn as in the model of Birkner et al. Let $c_N$ be the probability that two genes sampled from distinct individuals coalesce one generation back, and $\Phi_N$ the law of the ranked offspring frequencies $\big(V_{(1)}/2N, V_{(2)}/2N, \dots\big)$ on the simplex $\Delta = \{x_1 \ge x_2 \ge \dots \ge 0,\ \sum x_i \le 1\}$, with $\langle x, x\rangle = \sum_i x_i^2$. Assume $c_N \to 0$ and $\frac{1}{2c_N}\Phi_N(dx) \to \langle x,x\rangle^{-1}\Xi'(dx)$ vaguely on $\Delta \setminus \{\mathbf 0\}$, and set $\Xi = \Xi' \circ \varphi^{-1}$, where $\varphi$ splits each large family fraction $x_i$ into two equal parts for the two gene copies of the parent (so that a $\varphi(x)$-merger merges a given pair with probability $\langle x,x\rangle/2$). Let $\Pi^{N,n}_g$ be the partition of $n$ sampled genes by common ancestry $g$ generations back.

**Annealed limit (Birkner et al.).** Averaging over pedigrees, $\Pi^{N,n}_{\lfloor t/c_N\rfloor}$ converges in finite-dimensional distributions to an $n$-$\Xi$-coalescent.

**Theorem (quenched limit).** Assume in addition $\int_\Delta \langle x,x\rangle^{-1}\Xi(dx) < \infty$, and let $\Psi$ be a Poisson point process on $[0,\infty) \times (\Delta \setminus \{\mathbf 0\})$ with intensity $dt \otimes \langle x,x\rangle^{-1}\Xi(dx)$; put $c_{\mathrm{pair}} = 1 - \Xi(\Delta \setminus \{\mathbf 0\})$. The *inhomogeneous $(\Psi, c_{\mathrm{pair}})$-coalescent* $\Pi^n$ on partitions of $[n]$ performs, given $\Psi$, an $x$-paintbox merger at each atom $(t, x)$ of $\Psi$, and in addition merges each pair of blocks at rate $c_{\mathrm{pair}}$ independently of $\Psi$. Then, conditionally on the pedigree $\mathcal{A}^{(N)}$, for all times $t_1, \dots, t_k > 0$ and partitions $\xi_1, \dots, \xi_k$,
$$\mathbb{P}^{(N)}\big(\Pi^{N,n}_{\lfloor t_1/c_N\rfloor} = \xi_1, \dots, \Pi^{N,n}_{\lfloor t_k/c_N\rfloor} = \xi_k \,\big|\, \mathcal{A}^{(N)}\big) \to \mathbf{P}\big(\Pi^n_{t_1} = \xi_1, \dots, \Pi^n_{t_k} = \xi_k \,\big|\, \Psi\big)$$
in distribution as $N \to \infty$. Averaging over $\Psi$ recovers the $\Xi$-coalescent.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescent-theory/coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

In a fixed pedigree, the generations in which one couple produces a non-negligible fraction of the population are frozen features of the shared history: every gene genealogy sampled in that pedigree sees the same large-family events at the same times, which become the fixed atoms of $\Psi$. Ordinary generations contribute only diffuse pairwise coalescence, which self-averages across the many small families, giving a homogeneous Kingman component at rate $c_{\mathrm{pair}}$. So the pedigree matters exactly through the multiple-merger events: unlinked loci in one population share their multiple-merger times, which induces correlations between gene trees that the annealed $\Xi$-coalescent hides.

## Sources

- F. Alberti, M. Birkner, W.-T. L. Fan, J. Wakeley, "A conditional coalescent for diploid exchangeable population models given the pedigree", arXiv:2505.15481 (2025), Section 3 assumptions, Definition 3.6, Theorem 3.8 and Corollary 3.12, <https://doi.org/10.48550/arXiv.2505.15481>.
