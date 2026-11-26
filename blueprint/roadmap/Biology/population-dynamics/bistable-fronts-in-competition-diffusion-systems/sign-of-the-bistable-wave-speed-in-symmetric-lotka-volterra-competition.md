# Sign of the bistable wave speed in symmetric Lotka-Volterra competition

**Model.** Two species with identical demography and symmetric competition intensity $k$, differing only in diffusion rate, after scaling:

$$u_t=u_{xx}+u(1-u-kv),\qquad v_t=dv_{xx}+v(1-v-ku).$$

Under **strong competition**, $k>1$, both single-species states $(1,0)$ and $(0,1)$ are stable and coexistence is unstable (bistability). A monotone travelling front $(u,v)=(U,V)(x-ct)$ solves

$$U''+cU'+U(1-U-kV)=0,\qquad dV''+cV'+V(1-V-kU)=0,$$

with $(U,V)(-\infty)=(1,0)$, $(U,V)(+\infty)=(0,1)$, $U'<0<V'$. The sign of $c$ decides invasion: $c<0$ means $v$ advances and $u$ is locally excluded.

**Theorem (existence, uniqueness, smoothness).** For every $k>1$, $d>0$ there is a unique speed $c_{k,d}$ admitting a monotone front; the profile is unique up to translation, $C^\infty$, with $0<U,V<1$, and $-2\sqrt d<c_{k,d}<2$. The map $(k,d)\mapsto c_{k,d}$ is $C^\infty$ on $(1,\infty)\times(0,\infty)$, and the normalized front depends smoothly on $(k,d)$.

**Theorem ("unity is not strength").** For every $k>1$ and $d>0$,

$$\operatorname{sign}c_{k,d}=\operatorname{sign}(1-d):$$

the front moves so as to enlarge the territory of the **faster-diffusing** species, and $c_{k,d}=0$ iff $d=1$.

## Depends on

- [Fisher-KPP travelling waves](../../pattern-formation/fisher-kpp-travelling-waves/README.md)

## Expansion

The key step excludes standing fronts when $d\ne1$. Integral identities obtained from the two profile equations show that a front with $c=0$ must satisfy $(1-d)\int U''V'=0$, while a second identity gives $\int U''V'=\frac1{2d}\int(1-U-V)^2(-U')\ge\frac{(k-1)^2}{24dk^2}>0$. Hence $d=1$. Monotone standing fronts also satisfy $U+V<1$ with $\max(1-U-V)\ge\frac{k-1}{3k}$. Continuity then forces $c_{k,d}$ to have constant sign on each connected region $\{d<1\}$ and $\{d>1\}$ of parameter space. The sign is fixed by an explicit front: at $k=11/6$, $d=11/2$, with $\phi=1/(1+e^{\xi/\sqrt6})$, the pair $U=\phi^2$, $V=1-\phi$ is a front with $c=-\sqrt6/12<0$. The species-exchange symmetry gives $c_{k,d}=-\sqrt d\,c_{k,1/d}$, which transfers the sign to $d<1$. The smooth dependence comes from an implicit-function argument on exponentially weighted spaces using the exponential convergence of fronts to their end states. Biologically, faster random dispersal is advantageous in this symmetric setting, even though it spreads the population thinner.

## Sources

- C. Kenne, "Complete characterization of the sign of the wave speed in the symmetric Lotka-Volterra system under strong competition", arXiv:2608.16845 (2026), Theorem 1.1, Section 3 (Theorems 3.1-3.2, Lemma 3.3, Proposition 3.4, Lemma 3.5), Section 4 (Theorem 4.1, Corollary 4.2), Section 5 (Propositions 5.1-5.2) and Appendix A (Lemma A.1), <https://doi.org/10.48550/arXiv.2608.16845>.
