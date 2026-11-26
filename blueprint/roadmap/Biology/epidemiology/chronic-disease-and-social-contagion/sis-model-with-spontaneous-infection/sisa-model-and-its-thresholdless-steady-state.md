# SISa model: SIS contagion with spontaneous infection has no epidemic threshold

The SISa model extends the SIS model by letting susceptible individuals become infected spontaneously, independently of contacts. In a well-mixed population of constant size $N$ with $S + I = N$, transmission rate $\beta \ge 0$, recovery rate $\gamma > 0$ and spontaneous infection rate $\alpha \ge 0$,

$$\dot S = -\beta \frac{S I}{N} - \alpha S + \gamma I, \qquad \dot I = \beta \frac{S I}{N} + \alpha S - \gamma I.$$

Write $i = I/N \in [0, 1]$, so that $\dot i = q(i)$ with $q(i) = \beta i (1 - i) + \alpha (1 - i) - \gamma i$. If $\alpha > 0$ then:

1. $q$ has exactly one zero in $[0, 1]$, the steady-state prevalence

$$i^* = \frac{(\beta - \alpha - \gamma) + \sqrt{(\beta - \alpha - \gamma)^2 + 4 \alpha \beta}}{2 \beta} \quad (\beta > 0), \qquad i^* = \frac{\alpha}{\alpha + \gamma} \quad (\beta = 0),$$

and $0 < i^* < 1$;
2. every solution with $i(0) \in [0, 1]$ converges to $i^*$;
3. $i^*$ increases strictly in $\beta$ and in $\alpha$, decreases strictly in $\gamma$, and $i^* \ge \alpha/(\alpha + \gamma)$.

In particular the prevalence is positive for every $\beta$: unlike the SIS model with $R_0 = \beta/\gamma$, there is no threshold below which the "infection" dies out. With $\alpha = 0$ the model reduces to the SIS model, with $i^* = \max(0, 1 - \gamma/\beta)$.

## Depends on

- [Solution of the SIS system](../../sis-epidemic-model/is-solution.md)
- [Basic reproduction number of the SIS model](../../sis-epidemic-model/r0-eq.md)
- [Threshold theorem for the SIS model](../../sis-epidemic-model/deriv-infected-pos-iff.md)

## Proof depends on

- [Implicit function theorem](../../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md)
- [Endemic limit of every SIS solution](../../sis-epidemic-model/tendsto-infected-endemic.md)
- [Extinction for every SIS solution](../../sis-epidemic-model/tendsto-infected-zero.md)

## Proof sketch

$q$ is a concave quadratic, $q(i) = -\beta i^2 + (\beta - \alpha - \gamma) i + \alpha$, with $q(0) = \alpha > 0$ and $q(1) = -\gamma < 0$, so it has a single root in $(0, 1)$, the larger root of the quadratic; $q > 0$ below it and $q < 0$ above it, which gives global convergence for this scalar equation. Monotonicity follows from the implicit function theorem: $\partial_\beta q = i(1-i) > 0$, $\partial_\alpha q = 1 - i > 0$, $\partial_\gamma q = -i < 0$ at $i^*$, and $q'(i^*) < 0$; evaluating $q$ at $\alpha/(\alpha+\gamma)$ gives $\beta i (1 - i) \ge 0$, which gives the lower bound. The model was built for social contagion of behaviors and health states, with obesity as the case study: spontaneous adoption is caused by factors other than contacts. Interventions that only push the contact-driven reproduction number below one, such as vaccination-like "pinning", therefore cannot eliminate the trait. On a contact network, pairwise moment-closure equations show that clustering of infected individuals reduces the number of susceptible–infected edges below the random-mixing value, which lowers the effective transmission rate and the prevalence. This network effect fades as spontaneous infection dominates.

## Sources

- A. L. Hill, D. G. Rand, M. A. Nowak and N. A. Christakis, "Infectious disease modeling of social contagion in networks", PLoS Computational Biology 6 (2010) e1000968, Methods ("Application to social contagion", Equations 1–2; "Approximate pair-wise equations", Equations 4–9) and Results ("General properties of SISa model"), <https://doi.org/10.1371/journal.pcbi.1000968>, PMCID: PMC2973808.
