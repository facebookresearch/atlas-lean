# Endemic periodic orbit of a seasonal predator-prey model with disease in the prey

**Model.** Let $S$, $I$, $P$ be susceptible prey, infected prey and predators. With $\omega$-periodic, nonnegative, continuous rates (prey recruitment $\Lambda$, prey death $\mu$, predation on susceptibles $a$, incidence $\beta$, predation on infected prey $\eta$, infected removal $c \ge \mu$, conversion efficiencies $\gamma$ and $\theta$, predator logistic parameters $r$ and $b$) and a functional response $f(S,P)$,

$$\begin{aligned} S' &= \Lambda(t) - \mu(t) S - a(t) f(S,P) P - \beta(t) S I,\\ I' &= \beta(t) S I - \eta(t) P I - c(t) I,\\ P' &= \bigl(r(t) - b(t) P\bigr) P + \gamma(t) a(t) f(S,P) P + \theta(t)\eta(t) P I. \end{aligned}$$

Only susceptible prey reproduce. Write $\bar h = \frac1\omega\int_0^\omega h$. Assume (S1-S8) that $f \ge 0$ is continuous, nondecreasing in $S$ and nonincreasing in $P$, with $\bar\beta\, \partial_S f + \eta\, \partial_P f \ge 0$, $x \mapsto f(C_1 x + C_2, x)$ nondecreasing for $C_1, C_2 > 0$, $f(x,0) \le K x^\alpha$ for some $\alpha \ge 1$, and $\bar\Lambda, \bar\mu, \bar r, \bar b > 0$.

**Auxiliary systems.** For $\lambda \in (0,1]$, $x' = \lambda(\Lambda(t) - \mu(t) x)$ and $z' = \lambda(r(t) - b(t) z) z$ each have a unique globally asymptotically stable positive $\omega$-periodic solution (Lemmas 1 and 2). Assume (S9) that for each $\lambda \in (0,1]$ and small $\varepsilon_1, \varepsilon_2 \ge 0$, the disease-free predator-prey system

$$x' = \lambda\bigl(\Lambda - \mu x - a f(x,z) z - \varepsilon_1 x\bigr), \qquad z' = \lambda\bigl(\gamma a f(x,z) + r - b z + \varepsilon_2\bigr) z$$

has a unique positive, globally asymptotically stable $\omega$-periodic solution depending continuously on $(\varepsilon_1, \varepsilon_2)$; write $(x^*_\lambda, z^*_\lambda)$ for it at $\varepsilon_1 = \varepsilon_2 = 0$. Define

$$\overline{\mathcal R}_0 = \frac{\bar\beta \bar\Lambda/\bar\mu}{\bar c + \bar\eta \bar r/\bar b}, \qquad \mathcal R_0^\lambda = \frac{\overline{\beta x^*_\lambda}}{\bar c + \overline{\eta z^*_\lambda}}, \qquad \widetilde{\mathcal R}_0 = \inf_{\lambda \in (0,1]} \mathcal R_0^\lambda.$$

**Theorem 1 (existence of an endemic periodic orbit).** If $\widetilde{\mathcal R}_0 > 1$, $\overline{\gamma a}\,\bar\beta - \overline{\theta\eta}\,\bar a \le 0$ and

$$\overline{\mathcal R}_0 > 1 + \frac{\bar\beta}{\bar\mu}\Bigl(\frac{\bar a\,\bar r}{\bar\eta\,\bar r + \bar c\,\bar b} - \frac{\overline{\gamma a}}{\overline{\theta\eta}}\Bigr) f\Bigl(\frac{\bar\eta\,\bar r/\bar b + \bar c}{\bar\beta},\ \frac{\bar r}{\bar b}\Bigr),$$

then the system has an $\omega$-periodic orbit with $S, I, P > 0$.

**Corollaries 1 and 2 (special cases).** Without predation on susceptible prey ($a \equiv 0$), the conditions reduce to $\widetilde{\mathcal R}_0 > 1$ and $\overline{\mathcal R}_0 > 1$. For the Holling type I response $f(S,P) = S$ with constant $\Lambda, \mu, a, \gamma, r, \theta, b$ and periodic $\beta, \eta, c$, an endemic $\omega$-periodic orbit exists if $\Lambda < \mu^2/a$, $\gamma\bar\beta - \theta\bar\eta \le 0$, $\widetilde{\mathcal R}_0 > 1$ and

$$\overline{\mathcal R}_0 > 1 + \frac{a\bigl(r\theta\bar\eta - \gamma\bar\eta r - \gamma\bar c b\bigr)}{\mu\,\bar\eta\,\theta\, b}.$$

## Expansion

The proof applies Mawhin's continuation theorem. Embedding the system in the homotopy that multiplies the vector field by $\lambda \in (0,1]$, one first shows (Lemmas 3-5) that every positive $\omega$-periodic solution of every member satisfies uniform bounds $L_1, \dots, L_4$: upper bounds on $S$ and $P$ by comparison with the periodic solutions $x^*_\lambda$ and $z^*_\lambda$ of the one-dimensional auxiliary equations, and a lower bound on the infected class from $\widetilde{\mathcal R}_0 > 1$, which says that infection invades the disease-free periodic regime of every member of the family. In logarithmic variables the periodic problem becomes $\mathcal L u = \lambda \mathcal N u$ with $\mathcal L u = u'$ a Fredholm operator of index zero (Lemma 6) and $\mathcal N$ compact relative to it (Lemma 7). The a priori bounds keep solutions off the boundary of a ball $U$. The averaged (time-mean) algebraic system reduces to a scalar equation $G(P) = 0$ for the predator level with $G$ decreasing on $[\bar r/\bar b, \infty)$ and $G \to -\infty$; the displayed inequality in Theorem 1 is exactly $G(\bar r/\bar b) > 0$, so the averaged system has a unique zero. The sign condition $\overline{\gamma a}\,\bar\beta - \overline{\theta\eta}\,\bar a \le 0$ makes the Jacobian determinant there negative, so the Brouwer degree of the averaged map on $U \cap \ker\mathcal L$ is nonzero and Mawhin's theorem yields a periodic solution at $\lambda = 1$.

## Sources

- L. de Jesus, C. M. Silva, H. Vilarinho, "Periodic orbits for periodic eco-epidemiological systems with infected prey" (2020), Section 2 (model, hypotheses S1-S9, Lemmas 1 and 2), Section 3 (Theorem 1, Lemmas 3-7), Section 4 (Corollaries 1 and 2) and Appendix A (Mawhin's continuation theorem), <https://doi.org/10.48550/arXiv.2003.05697>.
