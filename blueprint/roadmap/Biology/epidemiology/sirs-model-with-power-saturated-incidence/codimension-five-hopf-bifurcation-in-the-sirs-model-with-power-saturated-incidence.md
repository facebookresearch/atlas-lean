# Codimension-five Hopf bifurcation in the SIRS model with power-saturated incidence

**Model.** The SIRS model with nonlinear incidence $kI^pS/(1+\alpha I^q)$, $p>0$, $q\ge 0$, is
$$S'=\Lambda-dS-\frac{kI^pS}{1+\alpha I^q}+\delta R,\qquad I'=\frac{kI^pS}{1+\alpha I^q}-(d+\mu)I,\qquad R'=\mu I-(d+\delta)R,$$
with positive rates. Since $N=S+I+R$ satisfies $N'=\Lambda-dN$, the plane $N=\Lambda/d$ is invariant and attracting, and the limit dynamics are those of the planar system
$$I'=\frac{kI^p}{1+\alpha I^q}\Big(\frac{\Lambda}{d}-I-R\Big)-(d+\mu)I,\qquad R'=\mu I-(d+\delta)R .$$

**Normalization.** Rescaling $I=\frac{\Lambda}{d}X$, $R=\frac{\mu\Lambda}{d(d+\delta)}Y$, $t'=(d+\delta)t$ gives $X'=\frac{k_1X^p}{1+bX^q}(1-X-sY)-rX$, $Y'=X-Y$ with $s=\mu/(d+\delta)>0$ and $s<r=(\mu+d)/(d+\delta)<s+1$. A positive equilibrium $(\tilde X,\tilde X)$ needs $0<\tilde X<1/(s+1)$; rescaling by $\tilde X$ moves it to $E_1=(1,1)$ and leaves the six independent parameters $p>0$, $q\ge 0$, $\tilde X$, $B\ge 0$, $s$, $r$. Keeping the coefficient of $x^p$ explicit removes exponentials in $p$ from the focus-value computations.

**Theorem.** There is an admissible parameter configuration for which $E_1$ is a nondegenerate weak focus of order five: the trace vanishes, the determinant is positive, the first four focus values vanish and the fifth does not, and the map from the parameters to the first five focus values has full rank there. Hence under an arbitrarily small admissible unfolding at least five small-amplitude limit cycles bifurcate from the positive equilibrium, and the Hopf bifurcation of the original SIRS model has codimension at least five. The authors also establish admissible generalized Hopf points with three and four small limit cycles.

**Conjecture.** No strictly admissible generalized-Hopf point has $V_1=\dots=V_5=0$, so five is the maximal number of small-amplitude limit cycles from the positive equilibrium in this family. Exact algebraic obstructions and extensive searches support it; no nonexistence theorem is claimed.

## Expansion

Small-amplitude limit cycles are counted with the Hopf normal form $\dot\rho=\rho(v_0+v_1\rho^2+\dots+v_k\rho^{2k}+\cdots)$: if $v_0=\dots=v_{k-1}=0\ne v_k$ at the critical parameters and the Jacobian of $(v_0,\dots,v_{k-1})$ with respect to $k$ parameters is nonsingular, then $k$ small cycles can be produced. Here the focus values are polynomial in the scaled parameters, so the focus conditions become polynomial equations with semialgebraic admissibility constraints ($0<s<r<s+1$, $0<\tilde X<1/(s+1)$, $B\ge 0$). The order-five point is certified with validated interval computation in the strict interior of the admissible region, together with a full-rank unfolding. This answers the codimension question for the Hopf bifurcation that earlier work, which bounded the Bogdanov–Takens codimension by two, left open.

## Sources

- Pei Yu, Wanyue Tang and Yanni Zeng, "A codimension-5 Hopf bifurcation yielding 5 limit cycles in a SIRS epidemic model with nonlinear incidence", arXiv:2609.38874 (2026), Theorem 1.1, Lemma 4.1, Corollary 5.8 and Conjecture 5.9, <https://doi.org/10.48550/arXiv.2609.38874>.
