# Bautin and Bogdanov–Takens bifurcations of the power-incidence SIRS model

**Setting.** After restriction to the invariant plane $S+I+R=\Lambda/d$ and normalization of the positive equilibrium to $E_1=(1,1)$, the SIRS model with incidence $kI^pS/(1+\alpha I^q)$ becomes
$$x'=\frac{Kx^p}{1+Bx^q}\Big(\frac{1}{\tilde X}-x-sy\Big)-rx,\qquad y'=x-y,$$
with $p>0$, $q\ge 0$, $B\ge 0$, $0<\tilde X<1/(s+1)$, $0<s<r<s+1$ and $K[1-(1+s)\tilde X]=r\tilde X(1+B)$. Put $\tilde X_1=1-(s+1)\tilde X\in(0,1)$.

**Stability.** $E_1$ is locally asymptotically stable for $0<p\le 1$ (every $q\ge 0$, $B\ge 0$), and more generally in seven explicit parameter regions; a Hopf bifurcation from $E_1$ occurs on the curve $B=B_{\mathrm H}$ in two of them.

**Proposition (Bautin bifurcation, $q=0$).** With $q=0$ and $p>1$, the Jacobian at $E_1$ has trace $\mathrm{Tr}=\frac{1}{\tilde X_1}\{pr\tilde X_1-[r+1-(s+1+sr)\tilde X]\}$ and determinant $\det=\frac{r}{\tilde X_1}(1-p\tilde X_1)$, so $E_1$ is locally asymptotically stable for $p<\min\{p_{\mathrm H},1/\tilde X_1\}$ with $p_{\mathrm H}=\dfrac{r+1-(s+1+sr)\tilde X}{r\tilde X_1}$. At the Hopf point $p=p_{\mathrm H}$ (with $\det>0$) the first focus value $v_1$ vanishes, for $1<s<r<s+1$ and $\frac{1}{s+1+sr}<\tilde X<\frac{1}{s+1}$, at the unique value $\tilde X=\dfrac{r+2}{2(s+1+sr)}$, and there the second focus value is positive. Hence the Hopf bifurcation is a generalized Hopf (Bautin) bifurcation of codimension two: perturbing $p$ and $r$, two small-amplitude limit cycles bifurcate from $E_1$, the inner one stable and the outer one unstable, both surrounding the unstable equilibrium.

**Proposition (Bogdanov–Takens).** The Bogdanov–Takens bifurcation, where trace and determinant at $E_1$ vanish simultaneously, occurs at $E_1$ and has codimension exactly two for every admissible $(p,q)$.

## Expansion

With $q=0$ the saturation reduces to the constant factor $1/(1+B)$, so only the exponent $p$ shapes the nonlinearity, and the first two focus values are explicit rational functions of $(s,r,\tilde X)$; $v_1=0$ singles out one value of $\tilde X$ and $v_2>0$ there, which gives the Bautin picture of nested cycles with opposite stability. For Bogdanov–Takens, $\det=0$ gives $p_{\mathrm{bt}}=\frac{1+B+Bq\tilde X_1}{(1+B)\tilde X_1}$ and then $\mathrm{Tr}=0$ gives $r_{\mathrm{bt}}=\tilde X_1/(s\tilde X)$, admissible iff $\frac{1}{(s+1)^2}<\tilde X<\frac{1}{s^2+s+1}$. The Jacobian of $(\mathrm{Tr},\det)$ with respect to $(p,r)$ equals $1$ there, so $(p,r)$ is a nondegenerate unfolding, and the quadratic normal form $\dot y_1=y_2$, $\dot y_2=c_{20}y_1^2+c_{11}y_1y_2$ has coefficients whose numerators are quadratics in $\tilde X$ shown not to vanish on the admissible region, which bounds the codimension by two.

## Depends on

- [Codimension-five Hopf bifurcation in the SIRS model with power-saturated incidence](codimension-five-hopf-bifurcation-in-the-sirs-model-with-power-saturated-incidence.md)

## Sources

- Pei Yu, Wanyue Tang and Yanni Zeng, "A codimension-5 Hopf bifurcation yielding 5 limit cycles in a SIRS epidemic model with nonlinear incidence", arXiv:2609.38874 (2026), Proposition 3.1, Proposition 4.2 and Proposition 7.1, <https://doi.org/10.48550/arXiv.2609.38874>.
