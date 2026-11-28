# Extinction threshold and Fokker–Planck well-posedness of a drift–division tumor model

**Model.** Each tumor cell carries a trait $x\ge0$, its remaining time to division. The trait drifts towards the origin at unit speed (aging). At $x=0$ the cell splits into two cells whose times to division $(y,z)$ are drawn from a symmetric probability density $G(y,z)$ on $\mathbb R_+^2$ with marginal $g$. Independently, therapy kills each cell at constant rate $m\ge0$. A population state is a finite configuration $\gamma\subset\mathbb R_+$. Observables evolve by the backward Kolmogorov equation $\frac{d}{dt}F_t=L^*F_t$ with

$$(L^*F)(\gamma)=-(DF)(\gamma)+\sum_{x\in\gamma}m\big[F(\gamma\setminus x)-F(\gamma)\big]+\sum_{x\in\gamma}\delta(x)\int_{\mathbb R_+^2}G(y,z)\big[F(\gamma\setminus x\cup\{y,z\})-F(\gamma)\big]\,dy\,dz,$$

where $D$ is the drift (gradient) term. The dual Fokker–Planck equation $\frac{d}{dt}f_t=Lf_t$ governs the density $f_t$ of the state law on the configuration space.

**Branching threshold.** A cell survives its cycle of length $\tau$ with probability $e^{-m\tau}$ and then leaves two offspring. The mean offspring number is therefore $\langle a\rangle=2\widehat g(m)$, where $\widehat g(m)=\int_0^\infty e^{-m\tau}g(\tau)\,d\tau$ is the Laplace transform of the cycle-length density. Since $\widehat g$ is continuous and strictly decreasing with $\widehat g(0)=1$, there is a unique $m_*>0$ with $\widehat g(m_*)=\frac12$, and the lineage (Galton–Watson) process, whose offspring number is $0$ or $2$, is subcritical, $\langle a\rangle<1$, iff $\widehat g(m)<\frac12$, that is iff $m>m_*$. Subcriticality implies almost-sure extinction of the tumor, but it is not necessary: by the Galton–Watson extinction criterion, extinction is almost sure iff $\langle a\rangle\le1$, that is iff $m\ge m_*$. At the critical rate $m=m_*$ the process is critical and still dies out almost surely; for instance, exponential cycle lengths of rate $1$ and death rate $m=1$ give $0$ or $2$ offspring with probability $\frac12$ each, and the extinction probability, the smallest fixed point of $s\mapsto(1+s^2)/2$, is $1$. The source's strict condition $m>m_*$ is sufficient for extinction, not equivalent to it. For a Gamma$(k,\theta)$ cycle-length law, $\widehat g(m)=(1+m\theta)^{-k}$ and

$$m_*=\frac{2^{1/k}-1}{\theta}.$$

**Theorem.** Suppose that for some $b>0$ and $\beta\ge3$, with $\psi_\beta(x)=(1+x)^{-\beta}$,

$$G(x,y)\le b\big[\psi_{\beta+1}(x)\psi_\beta(y)+\psi_\beta(x)\psi_{\beta+1}(y)\big]\qquad(x,y\ge0).$$

Set $m_0=\frac{(\beta-1)(b-\beta)}{2\beta-5}$ if $b>\beta$ and $m_0=0$ otherwise, and $m_1=\max\{m_0,m_*\}$.

1. For every $m>m_0$ and every initial probability density $f_0$ in the positive cone of the domain of the free generator, the Fokker–Planck equation has a unique classical positive solution $f_t$ with $\|f_t\|=1$ for all $t$. So the evolution is an honest stochastic semigroup: no probability mass is lost to explosion.
2. For $m>m_1$ there is $\sigma>0$ such that $\|f_t\|_{\alpha,\sigma}\le\|f_0\|_{\alpha,\sigma}$ for all $t>0$. Here $\|f\|_{\alpha,\sigma}=\int|f(\gamma)|\,w_{\sigma,\alpha}(\gamma)\,\lambda(d\gamma)$ with weight $w_{\sigma,\alpha}(\gamma)=1+\sigma|\gamma|+\sum_{x\in\gamma}e^{-\alpha x}$. In particular the expected population size stays bounded in time, so a sufficiently strong therapy keeps the tumor under control.

## Expansion

The generator splits as $L=A+B$: $A$ collects the drift and loss terms (death and division-loss), and $B$ is the positive gain operator that creates the two offspring. For every $\varepsilon$ in the relevant range, $L_\varepsilon=A+\varepsilon B$ on the domain of $L$ generates a substochastic semigroup. By the Thieme–Voigt perturbation theory, $L$ then generates a positive semigroup $S$ obtained as a limit of these, and $f_t=S(t)f_0$. A priori $S$ is only substochastic, which would mean a dishonest evolution in which mass escapes. Honesty, meaning $\|f_t\|=1$, is proved under $m>m_0$ by a separate criterion for stochastic semigroups, and the decay condition on $G$ with $\beta\ge3$ makes the required estimates work. The weighted bound for $m>m_1$ uses the weight $w_{\sigma,\alpha}$, whose $|\gamma|$ part is controlled once the lineages are subcritical ($m>m_*$).

These are the branching computation (Section 2), the model definition, and the main theorem with its proof sketch (Section 3) of the source.

## Proof depends on

- [Galton–Watson extinction criterion](../../../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md)

## Sources

- Y. Kozitsky, K. Pilorz, "Modeling tumor growth: a simple individual-based model and its analysis", arXiv:2003.09342 (2020). <https://doi.org/10.48550/arXiv.2003.09342>
- Published version: Y. Kozitsky, K. Pilorz, "Modeling Tumor Growth: A Simple Individual-Based Model and Its Analysis", in *Order, Disorder and Criticality*, vol. 6, World Scientific (2020), 201–221, <https://doi.org/10.1142/9789811216220_0005>.
