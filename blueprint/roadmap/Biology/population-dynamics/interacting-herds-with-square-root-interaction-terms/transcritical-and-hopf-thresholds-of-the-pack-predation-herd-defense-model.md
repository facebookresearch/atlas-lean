# Transcritical and Hopf thresholds of the pack-predation herd-defense model

**Model.** Let $Q$ be a prey that gathers in herds and $P$ a specialist predator hunting in packs, interacting only through the edges of their groups:

$$
\frac{dQ}{d\tau} = r\Big(1-\frac{Q}{K}\Big)Q - q\sqrt{P}\sqrt{Q},\qquad
\frac{dP}{d\tau} = -mP + p\sqrt{P}\sqrt{Q},
$$

with $r,K,q,m,p>0$ and $p<q$. For $P,Q>0$ the substitution $X=\sqrt{Q/K}$, $Y=\frac{q}{2m}\sqrt{P/K}$, $t=m\tau$ and the parameters $e=\frac{r}{2m}$, $f=\frac{pq}{4m^2}$ give

$$
\frac{dX}{dt} = e(1-X^2)X - Y,\qquad \frac{dY}{dt} = -\frac12 Y + fX.
$$

**Theorem.**

1. All solutions are bounded.
2. The coexistence equilibrium $\widehat E_2=\Big(\sqrt{\tfrac{e-2f}{e}},\;2f\sqrt{\tfrac{e-2f}{e}}\Big)$ is feasible iff $e\ge 2f$. The origin $\widehat E_0$ of the rescaled system is locally asymptotically stable iff $e<2f$ and $e<\tfrac12$, and when stable it is globally asymptotically stable. A transcritical bifurcation occurs at $e^*=2f$, where $\widehat E_2$ emanates from the origin.
3. $\widehat E_2$ is locally asymptotically stable when $e>2f$ and $\operatorname{tr}J=-2e+6f-\tfrac12<0$ (that is, either $2f<e<\tfrac12$ with this trace condition, or $e>\max\{\tfrac12,3f-\tfrac14\}$), and unstable when $\tfrac12<e<3f-\tfrac14$.
4. *(Hopf threshold.)* A Hopf bifurcation occurs at $\widehat E_2$ when $e$ crosses $e^{\dagger}=3f-\tfrac14$, producing persistent predator–prey oscillations.

## Expansion

The Jacobian of the rescaled system is $\begin{pmatrix} e(1-3X^2) & -1\\ f & -\tfrac12\end{pmatrix}$. At the origin its characteristic polynomial is $\lambda^2+(\tfrac12-e)\lambda+f-\tfrac e2$, so the Routh–Hurwitz conditions are $2f>e$ and $e<\tfrac12$; the first one fails exactly when $\widehat E_2$ becomes feasible, giving the transcritical exchange. At $\widehat E_2$, $\det J=e-2f>0$ by feasibility and $\operatorname{tr}J=-2e+6f-\tfrac12$, so purely imaginary eigenvalues occur exactly on the line $e=3f-\tfrac14$. Global stability of the origin uses a positively invariant rectangle with corner $(L,2fL)$, $L>\max\{1,e/(3\sqrt3 f)\}$, and Poincaré–Bendixson. Unlike the classical Lotka–Volterra model with logistic prey, the origin can be an attractor here: in the original variables the square-root response is non-Lipschitz at $Q=0$, and prey herds can be driven to extinction in finite time.

## Sources

- D. Melchionda, E. Pastacaldi, C. Perri, E. Venturino, *Interacting population models with pack behavior*, arXiv:1403.4419 (2014). <https://doi.org/10.48550/arXiv.1403.4419> — Section 3 (rescaling), Section 5.2: Propositions 7–11 (boundedness, transcritical bifurcation, local and global stability, Hopf bifurcation).
