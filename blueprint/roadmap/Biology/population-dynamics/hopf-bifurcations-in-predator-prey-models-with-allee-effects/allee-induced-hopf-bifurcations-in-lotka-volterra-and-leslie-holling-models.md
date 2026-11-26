# Allee-induced Hopf bifurcations in Lotka-Volterra and Leslie-Holling models

**Weak Allee effect with logistic prey.** Consider
$$\dot x=\frac{x^2}{x+M}\Big(1-\frac xK\Big)-xy,\qquad \dot y=-pKy+xy,$$
with Allee parameter $M>0$ (per-capita prey growth $x/(x+M)$ vanishes at low density but stays positive), carrying capacity $K$ and predator starvation rate $pK$, $0<p<1$. The coexistence equilibrium is $E_0=\big(Kp,\frac{Kp(1-p)}{M+Kp}\big)$, and its Jacobian is traceless at
$$M_0=\frac{Kp^2}{1-2p},\qquad 0<p<\tfrac12,$$
with $\frac{d\operatorname{Re}\lambda}{dM}\big|_{M_0}=\frac{(1-2p)^3}{2Kp(1-p)^2}>0$ and frequency $\omega=\sqrt{Kp(1-2p)}$. Without the Allee effect ($M=0$) $E_0$ is stable, and for large $K$ the Allee term destabilizes it.

**Theorem.** For every $p\in(0,\frac12)$, $p\ne\frac14$, the system undergoes a Hopf bifurcation at $(E_0,M_0)$: supercritical (stable cycle) for $p>\frac14$ and subcritical for $p<\frac14$. At $p=\frac14$ the first Lyapunov coefficient vanishes, and for every $K>0$ except two exceptional values a codimension-two Bautin (generalized Hopf) bifurcation occurs, where stable and unstable cycles coexist and collide.

**Strong Allee effect.** In the two strong-Allee versions of the logistic Lotka-Volterra model (prey growth negative below a threshold), the boundary equilibria are unstable whenever a coexistence equilibrium exists. In the first version the system undergoes a subcritical Hopf bifurcation at $p=q$ ($q$ the strong-Allee parameter) for every $K>0$, $q\in(0,1)$, with $E_0$ stable for $p<q$. In the second, a Hopf bifurcation occurs at $(E_0,M_0)$ for every $K>0$, with $E_0$ stable for $M<M_0$; it is supercritical or subcritical according to the sign of an explicit coefficient $\beta(p,q)$.

**Leslie-Holling models.** For $\dot x=\frac{x^2}{x+M}-xy$, $\dot y=ry(1-\frac yx)$ with $0<M<1$, the unique positive equilibrium $(1-M,1-M)$ undergoes a non-degenerate supercritical Hopf bifurcation at $r_0=M(1-M)$, stable for $r>r_0$. For the strong-Allee version $\dot x=x-L-xy$, $\dot y=ry(1-\frac yx)$ with $0<L<\frac14$, there are two positive equilibria $E_{1,2}=\big(\frac{1\mp\sqrt{1-4L}}2,\frac{1\mp\sqrt{1-4L}}2\big)$. $E_1$ is a saddle when its trace vanishes, and $E_2$ undergoes a subcritical Hopf bifurcation at $r_{02}=\frac12(1-\sqrt{1-4L})$, with frequency $\omega=\sqrt{(\sqrt{1-4L}+4L-1)/2}$, stable for $r>r_{02}$.

## Depends on

- [Lotka-Volterra predator-prey model](../lotka-volterra-predator-prey-model/README.md)

## Expansion

Each result follows the Andronov-Hopf recipe: find the parameter value where the trace of the Jacobian at the coexistence equilibrium vanishes while the determinant stays positive, check transversality ($d\operatorname{Re}\lambda/d\mu\ne0$), and compute the first Lyapunov coefficient from the quadratic and cubic Taylor terms in normal-form coordinates; its sign decides super- versus subcriticality, and its zero locus ($p=\frac14$ in the weak-Allee model) signals a Bautin point, where the second Lyapunov coefficient determines the unfolding. The Allee term $x/(x+M)$ makes prey growth increasing at low density, which can reverse the stabilizing effect of logistic self-limitation and is the mechanism behind the destabilization. The models were motivated by liquidity-profit dynamics in economics (corridors of stability) but are standard ecological predator-prey systems.

## Sources

- M. Demetrian, R. Zimka, "Aggregate models of liquidity-profit dynamics", arXiv:2607.19422 (2026), Section 1.2 (Lemma 1), Section 2 (Theorems 2.1-2.2), Section 3 (Lemma 2, Theorem 3.1), Section 4 (Theorem 4.1), Section 5 (Theorem 5.1) and Section 6 (Theorem 6.1), <https://doi.org/10.48550/arXiv.2607.19422>.
