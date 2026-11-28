# Erosion–dislocation characterization of simple nested fragmentation processes

**Setting.** Nested partitions model gene lineages inside species lineages (trees within trees). A **nested partition** of $\mathbb{N}$ is a pair $(\zeta,\xi)$ of partitions with $\zeta$ finer than $\xi$: the inner blocks of $\zeta$ (gene lineages) are grouped into outer blocks of $\xi$ (species). A **nested fragmentation** is a càdlàg Markov process $\Pi(t) = (\zeta(t),\xi(t))$ in the space of nested partitions of $\mathbb{N}$ whose paths are decreasing (blocks only split), which is **strongly exchangeable** (its law and transition kernel are invariant under injections of $\mathbb{N}$, equivalently every restriction to $[n]$ is a Markov chain), and which is **simple**: it has the *outer branching property* (distinct outer blocks fragment independently with the same law) and the *inner branching property* (within an outer block, distinct inner blocks behave independently with the same law). Write $\mathcal{S}^\downarrow$ for mass partitions $\mathbf{s} = (s_1 \ge s_2 \ge \dots \ge 0)$, $\sum s_i \le 1$.

For univariate exchangeable fragmentations, Bertoin's theorem says the jump measure is $c\,\mathfrak{e} + \rho_\nu$, with erosion rate $c \ge 0$ and a dislocation measure $\nu$ on $\mathcal{S}^\downarrow$ satisfying

$$\int_{\mathcal{S}^\downarrow}(1 - s_1)\,\nu(d\mathbf{s}) < \infty,$$

where $\rho_\nu$ mixes Kingman paintbox laws.

**Theorem.** The law of a simple nested fragmentation is characterized by a measure $\mu$ (its jump measure for the process started from a nested partition with infinitely many infinite inner blocks), and there exist

- an outer erosion coefficient $c_{\mathrm{out}} \ge 0$ and two inner erosion coefficients $c_{\mathrm{in},1}, c_{\mathrm{in},2} \ge 0$,
- an outer dislocation measure $\nu_{\mathrm{out}}$ on $\mathcal{S}^\downarrow$ with $\int (1 - s_1)\,\nu_{\mathrm{out}}(d\mathbf{s}) < \infty$,
- an inner dislocation measure $\nu_{\mathrm{in}}$ on nested mass partitions $\mathbf{p} = (\bar u, (u_l), (\bar s_k), (s_{k,l}))$ with $\nu_{\mathrm{in}}(\{\mathbf{1}\}) = 0$ and $\int (1 - u_1)\,\nu_{\mathrm{in}}(d\mathbf{p}) < \infty$,

such that

$$\mu = c_{\mathrm{out}}\,\mathfrak{e}^{\mathrm{out}} + c_{\mathrm{in},1}\,\mathfrak{e}^{\mathrm{in},1} + c_{\mathrm{in},2}\,\mathfrak{e}^{\mathrm{in},2} + \widehat{\rho}_{\nu_{\mathrm{out}}} + \widetilde{\rho}_{\nu_{\mathrm{in}}}.$$

The five components describe the possible jumps:

1. **outer erosion** (rate $c_{\mathrm{out}}$): a whole inner block leaves its outer block and forms a new outer block on its own;
2. **inner erosion** (rate $c_{\mathrm{in},1}$): a single element leaves its inner block, staying in the same outer block;
3. **inner erosion with a new species** (rate $c_{\mathrm{in},2}$): a single element leaves both its inner and outer block;
4. **outer dislocation** $\widehat{\rho}_{\nu_{\mathrm{out}}}$: an outer block splits by a paintbox with frequencies $\mathbf{s}$ applied to its inner blocks, which move as wholes;
5. **inner dislocation** $\widetilde{\rho}_{\nu_{\mathrm{in}}}$, specific to the nested setting: one inner block is shattered by a bivariate paintbox, its pieces being assigned to a distinguished part of the old outer block (frequency $\bar u$, inner pieces $u_l$) or to new outer blocks (frequencies $\bar s_k$, inner pieces $s_{k,l}$).

## Depends on

- [Kingman's paintbox representation of exchangeable random partitions](../../../../Probability/foundations/exchangeable-random-partitions/kingman-paintbox-representation-of-exchangeable.md)

## Expansion

Strong exchangeability makes every restriction to $[n]$ a finite Markov chain, so the process is described by a single exchangeable kernel; the outer branching property reduces this kernel to its value at the trivial outer partition, which, after relabelling the infinitely many infinite inner blocks as rows of $\mathbb{N}^2$, becomes a measure $\mu$ on nested partitions of $\mathbb{N}^2$ invariant under row-wise injections, with finite mass on events visible in $[n]^2$. Adding the inner branching property forces each jump to involve either one outer block acting on whole inner blocks (outer erosion or dislocation, which looks like a univariate fragmentation of the rows) or one inner block (inner erosion or dislocation). A de Finetti argument on the exchangeable row and column structure, as in Kingman's paintbox theorem and Bertoin's decomposition, shows that the non-erosive part of each type is a mixture of paintboxes, and the integrability conditions are exactly the finiteness of rates seen on $[n]^2$.

## Sources

- Jean-Jil Duchamps, "Trees within trees II: Nested fragmentations", *Ann. Inst. Henri Poincaré Probab. Stat.* 56(2) (2020), 1203–1229. <https://doi.org/10.1214/19-AIHP999>
- Preprint version (the locators in this item follow its numbering): Jean-Jil Duchamps, "Trees within trees II: Nested fragmentations", arXiv:1807.05951 (2018), Theorem 13 (outer branching characterization) and Theorem 17 (simple nested fragmentations), with the examples of Section 5.1, <https://doi.org/10.48550/arXiv.1807.05951>.
