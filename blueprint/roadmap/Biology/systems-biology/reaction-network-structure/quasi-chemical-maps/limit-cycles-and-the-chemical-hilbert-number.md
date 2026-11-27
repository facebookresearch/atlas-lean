# Limit cycles and the chemical Hilbert number

**Setting.** Let $H(n)$ be the Hilbert number: the supremum of the number of limit cycles of planar polynomial vector fields of degree $n$ (possibly infinite). Let $H_{\mathcal C}(n)$ be the analogous supremum over planar *chemical* polynomial vector fields of degree $n$, i.e. two-species mass-action reaction networks with reactions of order at most $n$.

**Theorem 5.4.** For every integer $n\ge2$,

$$H(n-1)\le H_{\mathcal C}(n)\le H(n).$$

**Corollary 5.1.** $H_{\mathcal C}(3)\ge4$, $H_{\mathcal C}(4)\ge13$, $H_{\mathcal C}(5)\ge28$, and $H_{\mathcal C}(n)$ grows like $n^2\ln n$ in the sense of the known lower bounds for $H(n-1)$.

**Theorem 5.1 (arbitrarily many limit cycles).** For the two-species network

$$\varnothing\rightleftharpoons X_1,\quad 2X_1\rightleftharpoons3X_1,\ \dots,\ 2nX_1\rightleftharpoons(2n+1)X_1,\quad X_2\to X_1+2X_2,\quad X_1+X_2\to X_1,$$

and any radii $0<r_1<\dots<r_n$, there are rate constants for which the mass-action system has $n$ nested hyperbolic limit cycles, the $i$th arbitrarily close to a circle of radius $r_i$ (after translation) with period close to $2\pi$, alternating in stability with the outermost one stable.

Theorems 5.2 and 5.3 give explicit networks whose mass-action dynamics contain a Lorenz-type chaotic attractor and a homoclinic bifurcation, respectively.

## Depends on

- [Quasi-chemical map preserves robust dynamics](quasi-chemical-map-preserves-robust-dynamics.md)

## Expansion

The upper bound is immediate since chemical systems are polynomial. For the lower bound, planar polynomial systems of degree $n-1$ realizing $H(n-1)$ limit cycles can be taken with all cycles hyperbolic, hence robust on a compact set containing them; the quasi-chemical map raises the degree by one and preserves every hyperbolic limit cycle, giving a chemical system of degree $n$ with the same number of cycles. Theorem 5.1 applies the same map to a planar polynomial oscillator whose hyperbolic limit cycles are placed near the prescribed radii; only the species $X_1$ carries the high-order autocatalytic steps that encode the polynomial damping.

## Sources

- T. Plesa, "Mapping dynamical systems into chemical reactions", *Nonlinear Dynamics* 113(22) (2025), 31149–31173, Theorems 5.1–5.4 and Corollary 5.1, <https://doi.org/10.1007/s11071-025-11622-1> (preprint arXiv:2406.03473).
