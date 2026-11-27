# Asymptotic counts of time-consistent galled trees

**Setting.** A galled tree is a rooted binary phylogenetic network in which every reticulation lies in its own cycle (gall), and the cycles are vertex-disjoint; it is *time-consistent* if the network can be drawn with node times so that the two parents of each reticulation are contemporaneous. Let $E_{n,g}$ be the number of unlabeled time-consistent galled trees with $n$ leaves and $g$ galls, and $e_{n,g}$ the number with $n$ labelled leaves. The unlabeled rooted binary trees (the case $g=0$) are counted by $U(t) = t + \frac12[U(t)^2 + U(t^2)]$, with $U_n \sim \frac{\gamma}{2\sqrt\pi}n^{-3/2}\rho^{-n}$ for Otter's constants $\gamma\approx1.13000$ and $\rho\approx0.4027$.

**Theorem.** For each fixed $g\ge 1$, as $n\to\infty$,

$$E_{n,g} \sim \frac{2^{2g-1}}{(2g)!\,\gamma^{4g-1}\sqrt\pi}\,n^{2g-\frac32}\rho^{-n},$$

$$e_{n,g} \sim \frac{2^{2g-1}}{(2g)!\sqrt\pi}\,n^{2g-\frac32}\,2^{n}\,n! \sim \frac{2^{2g-1}\sqrt2}{(2g)!}\Big(\frac2e\Big)^{n}n^{n+2g-1}.$$

The generating functions for fixed $g$ follow from a symbolic-method specification of galled trees in terms of trees and galls, and the unlabeled ones agree with those obtained earlier by a direct decomposition.

## Expansion

Each gall is specified by its sequence of pendant subtrees on the two sides of the cycle and the subtree below the reticulation, so the class is built from sequences and multisets of trees. The dominant singularity is that of the tree generating function, a square-root singularity at $\rho$ (unlabeled) or $1/2$ (labeled); each gall contributes a factor that raises the order of the pole in $(1-t/\rho)^{-1/2}$, producing the polynomial factor $n^{2g}$. Transfer theorems then give the asymptotics, and the labeled formula matches the leading behaviour $\frac{2^{k-1}\sqrt2}{k!}(2/e)^n n^{n+2k-1}$ shared by many network classes with $k$ reticulations.

## Sources

- L. Agranat-Tamir, M. Fuchs, B. Gittenberger, N. A. Rosenberg, "Enumerative combinatorics of unlabeled and labeled time-consistent galled trees", *Theoretical Computer Science* 1082 (2026), 116075, Sections 3–4 (generating functions and asymptotics for fixed numbers of galls), <https://doi.org/10.1016/j.tcs.2026.116075> (preprint arXiv:2504.16302).
