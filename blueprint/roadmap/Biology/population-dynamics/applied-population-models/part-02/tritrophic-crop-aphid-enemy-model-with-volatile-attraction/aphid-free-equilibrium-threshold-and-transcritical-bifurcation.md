# Aphid-free equilibrium threshold and transcritical bifurcation in a tritrophic model with volatile attraction

Consider crops $x$, aphids $y$ and aphid natural enemies $z$ governed by

$$
\begin{aligned}
\dot x&=rx\Big(1-\frac xK\Big)-a\frac{xy}{h+x},\\
\dot y&=y\Big(ae\frac{x}{h+x}-m-p\frac{z}{l+y}\Big),\\
\dot z&=x\Big(b+c\frac{y}{k+y}\Big)+z\Big(pq\frac{y}{l+y}-n\Big),
\end{aligned}
$$

where $r,K$ are the crop growth rate and carrying capacity, $a$ the maximal consumption rate of crop by aphids, $e$ and $q$ conversion yields, $m$ and $n$ the aphid and enemy mortality rates, $p$ the maximal uptake of aphids by enemies, $h,k,l$ half-saturation constants, $b\ge0$ the baseline attraction of enemies by crop volatile organic compounds (VOCs) and $c\ge0$ the extra attraction by VOCs released under aphid attack; all other parameters are positive. Solutions starting in $\mathbb R^3_+$ stay positive and enter the bounded region $\{x\le K_1,\ ex+y+z/q\le(er+\tfrac{b+c}{q}+1)K_1/\delta\}$ with $\delta=\min\{1/e,m,n\}$, $K_1=\max\{x_0,K\}$.

The system always has the collapse equilibrium $E_0=(0,0,0)$ and the aphid-free equilibrium

$$
E_1=\Big(K,\,0,\,\frac bnK\Big),
$$

in which crop volatiles alone sustain an enemy population.

**Theorem.** $E_0$ is unstable. If

$$
\frac{aeK}{h+K}<\frac{pbK}{nl}+m,
$$

then $E_1$ is locally asymptotically stable; if the reverse strict inequality holds, $E_1$ is unstable.

**Theorem (transcritical bifurcations).** Under an explicit nondegeneracy condition (stated in the source), the system undergoes a transcritical bifurcation at $E_1$ as the aphid mortality $m$ crosses

$$
m^*=\frac{aeK}{h+K}-\frac{pbK}{nl},
$$

and, equivalently, as the volatile attraction constant $b$ crosses

$$
b^*=\Big(\frac{aeK}{h+K}-m\Big)\frac{nl}{pK}.
$$

## Expansion

At $E_1$ the Jacobian is block triangular with eigenvalues $-r$, $-n$ and the aphid invasion rate $\frac{aeK}{h+K}-m-\frac{p}{l}\cdot\frac{bK}{n}$: an aphid entering a crop at carrying capacity grows at its conversion rate minus its mortality and minus the predation pressure of the volatile-sustained enemy population. The threshold is therefore an invasion criterion, and it shows that stronger constitutive volatile emission $b$ can by itself exclude the herbivore. When the invasion rate passes through zero an eigenvalue crosses $0$ and the aphid-free and coexistence branches exchange stability, which Sotomayor's theorem confirms as a transcritical bifurcation. The source also reports a saddle-node and a Hopf bifurcation of the coexistence equilibrium in $b$.

## Proof depends on

- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- Arturo J. Nic May, Eric J. Avila Vales. *Dynamics of tritrophic interaction with volatile compounds in plants* (2020), Sections 2–5: Lemmas 1–2, Section 4.1 (equilibria) and Theorems 1–3, 5–8. <https://doi.org/10.48550/arXiv.2003.07941>
