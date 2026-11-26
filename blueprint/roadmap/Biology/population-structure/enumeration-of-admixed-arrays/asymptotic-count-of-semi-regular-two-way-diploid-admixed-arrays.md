# Asymptotic count of semi-regular two-way diploid admixed arrays

**Setting.** A two-way diploid admixed array for $N$ individuals and $P$ loci is a pair $[\mathbf A,\mathbf X]$ of $N\times2P$ binary matrices: $A_{nj}\in\{0,1\}$ is the local ancestry and $X_{nj}\in\{0,1\}$ the allele on haplotype position $j$ (the two haplotype copies of locus $p$ are columns $p$ and $P+p$). The constraints are the *local ancestry tallies* $A^{(1)}_{n\cdot}=\sum_j\mathbf 1(A_{nj}=1)$ and the *ancestry-specific sums* $\Phi_{pk}=\sum_n\sum_{\ell\in\{0,1\}}\mathbf 1(A_{n,\ell P+p}=k)X_{n,\ell P+p}$, $k\in\{0,1\}$. In the semi-regular case all are uniform: $A^{(1)}_{n\cdot}=2P\bar a$ for every $n$ and $\Phi_{p0}=2Nf_0$, $\Phi_{p1}=2Nf_1$ for every $p$, with $f_1\le\bar a\le1-f_0$. Let $\mathscr A_1$, $\mathscr A_2$ and $\mathscr A_{12}$ be the arrays satisfying the first family, the second family and both.

**Theorem 3.4.** Fix $\bar a,f_0,f_1\in(0,1)$ with $f_1\le\bar a\le1-f_0$, and let $N,P\to\infty$ with $N/P$ bounded above and below. Then

$$|\mathscr A_{12}|=\frac{z_r}{(2\pi)^{D_r}}\,Q_r^{-2NP}\,e^{K_r}\,(1+o(1)),$$

with four cases $r$ according to whether $\bar a$ is interior to $[f_1,1-f_0]$, equals one endpoint, or both endpoints coincide. In the interior case

$$Q_1=(1-\bar a-f_0)^{1-\bar a-f_0}(\bar a-f_1)^{\bar a-f_1}f_1^{f_1}f_0^{f_0},\qquad D_1=N+2P,$$

so $\log|\mathscr A_{12}|=2NP\,H+O(\log NP)$, where $H$ is the Shannon entropy (natural log) of the frequencies $(f_1,\ \bar a-f_1,\ f_0,\ 1-\bar a-f_0)$ of the four (ancestry, allele) pairs; $z_1$ is an explicit Gaussian factor and $K_1=O(1)$. On the boundary one or two pair frequencies vanish and the Gaussian correction and dimension change ($D_2=D_3=N+2P-1$, $D_4=N+P-1$).

**Corollary 4.1 (edge $\bar a=f_1=1-f_0$).** With $\mathscr V$ the ambient set of arrays whose ancestry matrix has between $2NPf_1$ and $2NP(1-f_0)$ ones, $|\mathscr A_{12}|=\kappa_{N,P}\,|\mathscr V|^{-1}|\mathscr A_1||\mathscr A_2|$ with $\kappa_{N,P}\to e^{-1/4}$: the independence heuristic is off only by a bounded factor, a pointwise mutual information of $-1/(4\ln2)$ bits.

**Corollary 4.4.** In the other cases $\kappa_{N,P}$ has a finite positive limit only on the measure-zero set where an explicit entropy combination $\mathcal L(\bar a,f_0,f_1)$ vanishes (with additional conditions on $f_0,f_1$); elsewhere $\kappa_{N,P}\to0$ or $\infty$, so the information carried by the two summary families is generically not additive.

## Expansion

Proposition 2.3 counts each family exactly, and Theorem 2.4 writes $|\mathscr A_{12}|$ as a Cauchy coefficient integral of a product generating function over the torus. The integrand concentrates near a saddle point determined by the constraint frequencies; Isaev–McKay complex-martingale bounds (Theorem 3.1) justify the Gaussian approximation of the integral over the $D_r$ free directions, producing $Q_r^{-2NP}$ from the saddle value and $z_r$ from the Hessian determinant. Comparing the logarithms of $|\mathscr A_{12}|$ and $|\mathscr A_1||\mathscr A_2|/|\mathscr V|$ cancels the leading entropies only on the surface $\mathcal L=0$, and the $O(1)$ terms then decide the limiting correction.

## Sources

- A. J. Aw, "Semi-regular admixed arrays: asymptotic enumeration and when information is additive", arXiv preprint (2026), Proposition 2.3, Theorem 2.4, Theorems 3.1 and 3.4, Corollaries 4.1 and 4.4, <https://doi.org/10.48550/arXiv.2611.26990>.
