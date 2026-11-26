# Langmuir birth–death process of probe hybridization and the Langmuir-incomplete gamma law

**Deterministic and diffusion models.** In a probe region of an oligonucleotide microarray, let $u(t)\in(0,1)$ be the fraction of probe sites occupied by probe–target complexes. With target concentration $x$, adsorption constant $d_1$ and desorption constant $d_2$, the Langmuir equation is $\dot u=d_1x-(d_1x+d_2)u$, with steady state $u=d_1x/(d_1x+d_2)$. Its stochastic version $\dot u=d_1x-(d_1x+d_2)u+\sqrt{g(u)}\,Z_t$ with $g(u)=Cd_1xu$ has a gamma stationary density on $(0,\infty)$, which gives positive mass to the physically meaningless values $u>1$ and no mass to saturation $u=1$.

**Definition (Langmuir BD process).** A *Langmuir birth–death (LBD) process* is a birth–death process on $\{0,\dots,N\}$ (number of occupied sites) with rates

$$
b(k)=c_1(N-k)+\mathcal C(k,N),\qquad d(k)=c_2k+\mathcal C(k,N),\qquad k=0,\dots,N,
$$

with constants $c_1,c_2>0$ and a non-specific-hybridization noise term $\mathcal C(k,N)=\frac{N^2}{2}g(k/N)$ for $0<k<N$, subject to $\mathcal C(0,N)=\mathcal C(N,N)=0$. Three choices, with $c_3>0$:

- $M_1$: $\mathcal C_1(k,N)=c_3Nk$ for $0\le k<N$, $\mathcal C_1(N,N)=0$ (discrete analogue of the linear-noise Langmuir diffusion, with $c_1=d_1x$, $c_2=d_2$, $c_3=Cd_1x/2$);
- $M_2$: $\mathcal C_2(k,N)=c_3N(N-k)$ for $0<k\le N$, $\mathcal C_2(0,N)=0$ (the reflection of $M_1$, modeling a threshold effect);
- $M_3$: $\mathcal C_3(k,N)=c_3k(N-k)$ (smooth at both boundaries).

**Definition (LIG distribution).** For $\beta>\alpha>0$, let $\Gamma(\alpha,\beta)=\int_0^\beta s^{\alpha-1}e^{-s}\,ds$ and let $IG(\alpha,\beta,1)$ have density $\Gamma(\alpha,\beta)^{-1}\beta^\alpha x^{\alpha-1}e^{-\beta x}$ on $(0,1)$, with distribution function $F_{\alpha,\beta}$. The *Langmuir-incomplete gamma* law $LIG(\alpha,\beta)$ is the mixture

$$
G=(1-\pi_{\alpha,\beta})F_{\alpha,\beta}+\pi_{\alpha,\beta}\,\delta_1,\qquad \pi_{\alpha,\beta}=\frac{\beta^\alpha}{\beta^\alpha+\Gamma(\alpha,\beta)(\beta-\alpha)e^{\beta}},
$$

an incomplete gamma law on $(0,1)$ with an atom $\pi_{\alpha,\beta}$ at the saturated state $1$.

**Lemma (moments).** If $Z\sim LIG(\alpha,\beta)$ then for every integer $m\ge0$,

$$
\mathbb E Z^{m+1}=\frac{m+\alpha}{\beta}\,\mathbb EZ^m-\frac m\beta\,\pi_{\alpha,\beta};
$$

in particular $\mathbb EZ=\alpha/\beta$.

## Expansion

The linear terms $c_1(N-k)$ and $c_2k$ reproduce the deterministic Langmuir kinetics, while the higher-order term $\mathcal C$ models non-specific adsorption and desorption (for example competition between probes with similar sequences for the same targets). Keeping the state space finite fixes the defect of the diffusion model: the stationary law lives on $[0,1]$ and can charge the saturated state, matching microarray data where some probes saturate. The moment recursion follows from the incomplete gamma integration-by-parts identity together with the extra contribution of the atom at $1$.

## Sources

- Grzegorz A. Rempala, Iwona Pawlikowska. *Limit Theorems for Hybridization Reactions on Oligonucleotide Microarrays* (2008), Sections 2–3: Definitions 2.1 and 3.1, Theorem 1 and Lemmas 1–2. <https://doi.org/10.48550/arXiv.0802.1192>
