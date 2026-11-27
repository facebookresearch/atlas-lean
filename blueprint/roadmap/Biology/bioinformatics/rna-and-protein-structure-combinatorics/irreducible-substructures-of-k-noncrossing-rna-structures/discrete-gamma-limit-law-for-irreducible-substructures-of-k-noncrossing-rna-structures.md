# Discrete gamma limit law for irreducible substructures of $k$-noncrossing RNA structures

**Setting.** An RNA structure on $n$ nucleotides is a diagram on $[n]$: arcs (base pairs) $(i,j)$, $i<j$, drawn above the backbone, each vertex of degree at most $1$. It is **$k$-noncrossing** if it has no $k$ mutually crossing arcs ($k=2$ gives secondary structures; $k\ge3$ allows pseudoknots) and **$\sigma$-canonical** if every stack of consecutive nested parallel arcs has at least $\sigma$ arcs. Throughout, every arc $(i,j)$ has $j-i\ge4$ (minimum arc length $4$); $\mathbf T_k$, $\alpha_k$ and $\tau_k$ below depend on this restriction. Such diagrams correspond bijectively to vacillating tableaux with at most $k-1$ rows. A structure decomposes uniquely as a concatenation of unpaired gaps and **irreducible substructures**, blocks that cannot be cut at an interior backbone position without cutting an arc; these correspond to the returns of the tableau to the empty shape.

Let $\mathbf{T}_k(z)=\sum_n\delta^{(k)}_nz^n$ count $k$-noncrossing $\sigma$-canonical structures with arc length at least $4$, with real positive dominant singularity $\alpha_k$, and let $\xi^{(k)}_n$ be the number of irreducible substructures of a uniformly random such structure on $[n]$.

**Theorem.**

*(1)* *(Bivariate generating function.)* The generating function of structures counted by $z^{\text{length}}u^{\#\text{irreducible blocks}}$ is

$$\mathbf{U}_k(z,u)=\frac{1}{1-z-u\,\mathbf{R}_k(z)}=\frac{1/(1-z)}{1-u\left(1-\frac{1}{(1-z)\mathbf{T}_k(z)}\right)},\qquad \mathbf{R}_k(z)=1-z-\frac{1}{\mathbf{T}_k(z)} .$$

*(2)* *(Limit law.)* With $\tau_k=1-\dfrac{1}{(1-\alpha_k)\mathbf{T}_k(\alpha_k)}<1$,

$$\lim_{n\to\infty}\mathbb{P}\big(\xi^{(k)}_n=i\big)=q_i=\frac{(1-\tau_k)^2}{\tau_k}\,i\,\tau_k^{\,i},\qquad i\ge1,$$

a discrete $\Gamma(-\ln\tau_k,2)$ law, with probability generating function $q(u)=\dfrac{u(1-\tau_k)^2}{(1-\tau_ku)^2}$.

## Expansion

Writing $g(z)=1/(1-z)$ and $h(z)=1-1/\big((1-z)\mathbf{T}_k(z)\big)$, the decomposition into gaps and irreducible blocks gives $\mathbf{U}_k(z,u)=g(z)\,g(u\,h(z))$, a composition scheme. At $z=\alpha_k$, $h$ reaches $\tau_k<1=\rho_g$, so the scheme is subcritical: the singularity comes from $h$, which has a singular expansion $h(z)=\tau_k-c_k(1-z/\alpha_k)^{\mu}(1+o(1))$, with an extra logarithmic factor for odd $k$, where $\mu=(k-1)^2+\tfrac{k-1}{2}-1$. In the subcritical case the number of blocks converges in law to the distribution with probability generating function proportional to $u\,g'(\tau_ku)$, which is exactly $q(u)$. For Dyck paths, the analogous count of nontrivial returns has mean $(2n-2)/(n+2)$ (Shapiro).

## Sources

- Emma Y. Jin and Christian M. Reidys, "On the decomposition of $k$-noncrossing RNA structures", arXiv:0902.3783 (2009), Section 1 (definitions), the bivariate generating function lemma and the main limit-law theorem of Sections 3–4, <https://doi.org/10.48550/arXiv.0902.3783>.
