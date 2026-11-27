# Endemic periodic orbit of a seasonal predator-prey model with disease in the prey

**Model.** Let $S$, $I$, $P$ be susceptible prey, infected prey and predators. With $\omega$-periodic rates (prey recruitment $\Lambda$, prey death $\mu$, predation on susceptibles $a$, incidence $\beta$, predation on infected prey $\eta$, removal of infected prey $c$ with $c(t) > \mu(t)$, conversion efficiencies $\gamma$ and $\theta$, predator vital parameters $r$ and $b$) and a functional response $f(S,I,P)$,

$$\begin{aligned} S' &= \Lambda(t) - \mu(t) S - a(t) f(S,I,P) P - \beta(t) S I,\\ I' &= \beta(t) S I - \eta(t) P I - c(t) I,\\ P' &= \bigl(r(t) - b(t) P\bigr) P + \gamma(t) a(t) f(S,I,P) P + \theta(t)\eta(t) P I. \end{aligned}$$

Only susceptible prey reproduce. Write $\bar h = \frac1\omega\int_0^\omega h$.

**Hypotheses.**
- S1) $\Lambda,\mu,a,\beta,\eta,c,\gamma,\theta,b$ are $\omega$-periodic, nonnegative and continuous; $r$ is $\omega$-periodic and continuous, and either nonnegative or nonpositive.
- S2) $f$ is nonnegative and $C^1$.
- S3) $x\mapsto f(x,y,z)$ is nondecreasing.
- S4) $z\mapsto f(x,y,z)$ and $y\mapsto f(x,y,z)$ are nonincreasing.
- S5) For all $(x,y,z)$: $f+z\,\partial_zf>0$, $\ \bar\eta+\bar a\,\partial_yf>0$ and $\ \overline{\theta\eta}+\overline{\gamma a}\,\partial_yf>0$.
- S6) $\bar\Lambda>0$, $\bar\mu>0$ and $\bar b>0$.
- S7) There are $\alpha\ge1$ and $K>0$ with $f(x,0,0)\le Kx^\alpha$.
- S9) For each $\lambda\in(0,1]$ and all sufficiently small $\varepsilon_1,\varepsilon_2,\varepsilon_3,\varepsilon_4\ge0$, the disease-free system

$$x' = \lambda\bigl(\Lambda - \mu x - a f(x,\varepsilon_3,z) z - \varepsilon_1 x\bigr), \qquad z' = \lambda\bigl(\gamma a f(x,\varepsilon_4,z) + r - b z + \varepsilon_2\bigr) z$$

has a unique $\omega$-periodic solution with both components positive, globally asymptotically stable in $\{(x,z): x\ge0,\ z>0\}$ and depending continuously on $(\varepsilon_1,\varepsilon_2,\varepsilon_3,\varepsilon_4)$. Write $(x^*_\lambda, z^*_\lambda)$ for it at $\varepsilon_1=\varepsilon_2=\varepsilon_3=\varepsilon_4=0$.

The published list of hypotheses has no S8. Define

$$\overline{\mathcal R}_0 = \frac{\bar\beta \bar\Lambda/\bar\mu}{\bar c + \bar\eta \bar r/\bar b}, \qquad \mathcal R_0^\lambda = \frac{\overline{\beta x^*_\lambda}}{\bar c + \overline{\eta z^*_\lambda}}, \qquad \widetilde{\mathcal R}_0 = \inf_{\lambda \in (0,1]} \mathcal R_0^\lambda.$$

**Theorem (existence of an endemic periodic orbit).** Assume S1)–S7) and S9), $\widetilde{\mathcal R}_0 > 1$, and that the averaged system

$$S' = \bar\Lambda - \bar\mu S - \bar a f(S,I,P) P - \bar\beta S I,\qquad I' = \bar\beta S I - \bar\eta P I - \bar c I,\qquad P' = (\bar r - \bar b P) P + \overline{\gamma a} f(S,I,P) P + \overline{\theta\eta} P I$$

has a unique equilibrium in the open positive octant $(\mathbb R^+)^3$. Then the system has an $\omega$-periodic orbit with $S, I, P > 0$.

**Corollaries (special cases).** For the Holling type I response $f(S,I,P) = S$ with constant positive $\Lambda, \mu, r, b, \gamma, a$, assume S1) and S6). If $\widetilde{\mathcal R}_0 > 1$, $b\bar\beta - \gamma a\bar\eta > 0$, $\Lambda < \mu^2/a$ and

$$\overline{\mathcal R}_0 > 1 + \frac{a}{\mu}\Bigl(\frac{\bar\eta\gamma\Lambda}{r\bar\eta + b\bar c} + \frac{\bar\beta r + \gamma a\bar c}{b\bar\beta - \gamma a\bar\eta}\Bigr),$$

then an endemic $\omega$-periodic orbit exists. Without predation on susceptible prey ($f \equiv 0$), with $\Lambda,\mu,\beta,\eta,c,\gamma,r,\theta,b$ $\omega$-periodic, nonnegative and continuous and $\bar\Lambda, \bar\mu, \bar r, \bar b > 0$, the conditions $\widetilde{\mathcal R}_0 > 1$ and $\overline{\mathcal R}_0 > 1$ give an endemic $\omega$-periodic orbit.

## Expansion

The proof applies Mawhin's continuation theorem. Embedding the system in the homotopy that multiplies the vector field by $\lambda \in (0,1]$, one first shows that every positive $\omega$-periodic solution of every member satisfies uniform bounds: upper bounds on $S$ and $P$ by comparison with the periodic solutions of the auxiliary equations $x' = \lambda(\Lambda - \mu x)$ and $z' = \lambda(r - bz)z$, and a lower bound on the infected class from $\widetilde{\mathcal R}_0 > 1$, which says that infection invades the disease-free periodic regime of every member of the family. In logarithmic variables the periodic problem becomes $\mathcal L u = \lambda \mathcal N u$ with $\mathcal L u = u'$ a Fredholm operator of index zero and $\mathcal N$ compact relative to it. The a priori bounds keep solutions off the boundary of a ball, and the unique positive equilibrium of the averaged system gives a nonzero Brouwer degree on the kernel of $\mathcal L$, so Mawhin's theorem yields a periodic solution at $\lambda = 1$. For the Holling type I corollary, the averaged equilibrium equations reduce to a scalar equation $F(x)=0$ for $x=e^{u_3}$ with $F$ decreasing and $F\to-\infty$; the displayed inequality is $F>0$ at the left end of the admissible range, which gives the unique equilibrium, and $\Lambda<\mu^2/a$ makes a region positively invariant on which a divergence argument excludes periodic orbits of the disease-free system, which gives S9).

## Sources

- L. F. de Jesus, C. M. Silva, H. Vilarinho, "Periodic orbits for periodic eco-epidemiological systems with infected prey", Electron. J. Qual. Theory Differ. Equ. 2020, No. 54, 1–20, Section 2 (model (2.1), hypotheses S1)–S9), Lemmas 2.1–2.2, the numbers (2.5), the averaged system (2.6) and Theorem 2.3) and Section 3 (Corollaries 3.2 and 3.3), <https://doi.org/10.14232/ejqtde.2020.1.54>.
- The same authors' preprint, arXiv:2003.05697 (2020), Appendix A (Mawhin's continuation theorem), <https://doi.org/10.48550/arXiv.2003.05697>.
