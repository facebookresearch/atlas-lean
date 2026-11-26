# Media-delay-induced Hopf bifurcation in the SVIRS model

**Setting.** In the SVIRS model with delayed media-reduced transmission $\iota I e^{-mI(t-\tau)}$, waning vaccine and natural immunity, and saturated recovery $\gamma_0I/(1+\alpha I)$, assume $\mathcal R_0>1$ and the media-intensity bound that makes the endemic equilibrium $E^\ast$ unique, and assume (Routh–Hurwitz condition (H)) that $E^\ast$ is locally asymptotically stable at $\tau=0$. Linearizing at $E^\ast$ gives
$$\lambda^4+a_{11}\lambda^3+a_{12}\lambda^2+a_{13}\lambda+a_{14}+\big(a_{21}\lambda^3+a_{22}\lambda^2+a_{23}\lambda+a_{24}\big)e^{-\lambda\tau}=0 .$$
A root $\lambda=iw$, $w>0$, exists iff $z=w^2>0$ solves
$$H(z)=z^4+s_1z^3+s_2z^2+s_3z+s_4=0,$$
$s_1=a_{11}^2-2a_{12}-a_{21}^2$, $s_2=a_{12}^2+2a_{14}-2a_{11}a_{13}-a_{22}^2+2a_{21}a_{23}$, $s_3=a_{13}^2-2a_{12}a_{14}+2a_{22}a_{24}-a_{23}^2$, $s_4=a_{14}^2-a_{24}^2$. For each positive root $z_k$ with $w_k=\sqrt{z_k}$ there is an increasing sequence of critical delays $\tau_n^{(k)}\to\infty$ at which $\pm iw_k$ are roots; let $\tau_0$ be the smallest.

**Theorem.**
1. If $H$ has no positive root, $E^\ast$ is locally asymptotically stable for every $\tau\ge 0$ (absolute stability). $H$ has a positive root whenever $s_4<0$; for $s_4\ge 0$ explicit conditions from the resolvent cubic of $H$ decide.
2. If $H$ has a positive root, $E^\ast$ is locally asymptotically stable for $0\le\tau<\tau_0$ and unstable for $\tau>\tau_0$. If $H'(z_k)>0$, a Hopf bifurcation of periodic solutions occurs at $E^\ast$ as $\tau$ crosses $\tau_n^{(k)}$, since $\operatorname{sign}\frac{d\operatorname{Re}\lambda}{d\tau}\big|_{\tau_n^{(k)}}=\operatorname{sign}H'(z_k)$.
3. Normal-form quantities computed by center-manifold reduction determine whether the bifurcation is super- or subcritical, whether the bifurcating orbits are stable, and whether their period increases or decreases.
4. *(Global continuation.)* If moreover the global-stability condition (P) holds, the connected component of periodic orbits bifurcating from $(E^\ast,\tau_n^{(k)},2\pi/(w_k\tau_n^{(k)}))$ is unbounded in the delay direction, so for each $n$ nontrivial periodic solutions exist for arbitrarily large $\tau>\tau_n^{(k)}$.

## Expansion

Separating real and imaginary parts of the characteristic equation at $\lambda=iw$ and eliminating $\tau$ by $\sin^2+\cos^2=1$ produces the degree-eight even polynomial $H(w^2)$. Each positive root fixes a frequency, and the phase condition then gives a lattice of delays spaced by $2\pi/w_k$. The transversality sign reduces to $H'(z_k)$ divided by a positive quantity. Global continuation follows Wu's equivariant degree theory: bounded orbits and a period bounded between $\tau/(n+1)$ and $\tau$ force the continuum to be unbounded in $\tau$. Biologically, a slow public response to media reporting alone can turn a stable endemic state into recurrent outbreaks.

## Depends on

- [Equilibria and threshold stability of the delayed media SVIRS model](equilibria-and-threshold-stability-of-the-delayed-media-svirs-model.md)

## Sources

- Songbo Hou and Xinxin Tian, "Stability and Hopf Bifurcation of a Delayed SVIRS Epidemic Model with Media Coverage", arXiv:2608.22303 (2026), Theorem 3.2, Lemmas 5.1–5.2, Theorems 5.1, 5.2 and 6.1, <https://doi.org/10.48550/arXiv.2608.22303>.
