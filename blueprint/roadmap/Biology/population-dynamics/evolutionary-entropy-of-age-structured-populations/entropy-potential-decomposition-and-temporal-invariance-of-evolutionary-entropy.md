# Entropy–potential decomposition and temporal invariance of evolutionary entropy

**Setting.** Let $V(a)=\ell(a)m(a)\ge0$ be the net maternity function of an age-structured population and $r$ its Malthusian rate, the root of the Euler–Lotka equation $\int_0^\infty e^{-ra}V(a)\,da=1$. The *reproductive density* $p(a)=e^{-ra}V(a)$ is a probability density on $[0,\infty)$: the age distribution of mothers at birth in the stable population. Fix a reference duration $\tau>0$ (one year) and assume $0<T<\infty$ and finite entropies. Define
$$T=\int_0^\infty a\,p(a)\,da,\qquad S=-\int_0^\infty p(a)\log(\tau p(a))\,da,\qquad H=\frac{S}{T},\qquad \Phi=\frac1T\int_0^\infty p(a)\log(\tau V(a))\,da,$$
the generation time, cycle entropy, evolutionary entropy and reproductive potential.

**Proposition 1 (growth decomposition).** $r=H+\Phi$.

**Theorem 1 (change of time unit).** Under $\tilde a=ca$, $c>0$, with the reference duration expressed in the new unit, $\tilde S=S$, $\tilde T=cT$, $\tilde H=H/c$; likewise $\tilde\Phi=\Phi/c$ (Corollary 1).

**Theorem 2 (temporal aggregation).** Partition ages into classes $I_j=[jh,(j+1)h)$ and let $P_j=\int_{I_j}p$, $\varphi_j=p/P_j$ on $I_j$, $C_j=-\int_{I_j}\varphi_j\log(\tau\varphi_j)$ and $S_h=-\sum_jP_j\log P_j$. Then
$$S=S_h+\sum_{j\ge0}P_jC_j,$$
and the generation time is recovered exactly as $T=\sum_jP_j\bar a_j$ from the class means $\bar a_j$ (Proposition 2). For nested meshes $h_c=mh_f$ the reconstructed quantities agree: $S^{\rm rec}_{h_c}=S^{\rm rec}_{h_f}=S$ and $\frac{1}{h}\,S^{\rm rec}_h/T^{\rm class}_h=H$ for both meshes (Theorems 4–5), so evolutionary entropy is invariant under exact coarsening.

**Theorem 6 (continuous limit).** If $p$ is continuous with compact support, $\lim_{h\to0}\big(S_h+\log h\big)=S$ (with $\tau=1$), equivalently the Kullback–Leibler divergence from $p$ to its piecewise-uniform histogram tends to $0$; hence the corrected discrete evolutionary entropy converges to $H$ (Corollary 4).

## Expansion

Proposition 1 is a one-line identity: where $p>0$, $\log(\tau V(a))=ra+\log(\tau p(a))$; integrating against $p$ and dividing by $T$ gives $\Phi=r-S/T$. Under $\tilde a=ca$ the density becomes $\tilde p(\tilde a)=p(\tilde a/c)/c$ and the reference becomes $c\tau$, so $\tau p$ is unchanged and $S$ is invariant while $T$ scales by $c$. Theorem 2 is Shannon's chain rule: on $I_j$, $\log(\tau p)=\log P_j+\log(\tau\varphi_j)$, which splits the entropy into between-class and within-class parts. Theorem 6 says that the within-class entropies of a continuous density approach $\log h$ uniformly as classes shrink, so Leslie-matrix entropies computed at step $h$ must be corrected by $\log h$ before comparing species.

## Sources

- J. Buescu, H. M. Oliveira, "Temporal invariance of evolutionary entropy and comparative demographic analysis", arXiv preprint (2026), Proposition 1, Theorem 1, Corollary 1, Theorem 2, Proposition 2, Theorems 4–6 and Corollary 4, <https://doi.org/10.48550/arXiv.2610.15466>.
