# Global stability of the delayed SEIR model with health-care-capacity-dependent rates

**Setting.** Consider the reduced delay system of the [delayed SEIR model with health-care-capacity-dependent rates](reproduction-number-of-the-delayed-seir-model-with-health-care-capacity.md),

$$S'(t) = b - \beta S(t) I(t) - d S(t), \qquad I'(t) = k\, S(t - \tau) I(t - \tau) - K\, I(t), \qquad k = \gamma\beta e^{-d\tau},$$

with $b, d, \beta, \gamma, K > 0$, $\tau \ge 0$, nonnegative continuous initial histories on $[-\tau, 0]$, threshold $R_0 = b k /(d K)$, disease-free equilibrium $P_0 = (b/d, 0)$ and, for $R_0 > 1$, endemic equilibrium $P^* = (S^*, I^*)$.

**Theorem.** In the invariant region $\Gamma$ (where $S \le b/d$):

1. if $R_0 < 1$, $P_0$ is globally asymptotically stable;
2. if $R_0 > 1$, $P^*$ is globally asymptotically stable for solutions with $I \not\equiv 0$ on the initial interval.

## Depends on

- [Basic reproduction number of a delayed SEIR model with health-care-capacity-dependent rates](reproduction-number-of-the-delayed-seir-model-with-health-care-capacity.md)

## Expansion

*Disease-free case.* Take $L(t) = I(t) + k \int_{t-\tau}^{t} S(\theta) I(\theta)\, d\theta$. The delayed terms cancel and

$$L'(t) = I(t)\big(k S(t) - K\big) \le I(t)\big(k b/d - K\big) = K (R_0 - 1) I(t) \le 0 ,$$

using $S \le b/d$ in $\Gamma$. The largest invariant set in $\{L' = 0\}$ is $\{P_0\}$, and LaSalle's invariance principle gives global attractivity.

*Endemic case.* With $\phi(z) = z - 1 - \ln z \ge 0$, the equilibrium identities $b = \beta S^* I^* + d S^*$ and $K = k S^*$, a Volterra-type functional

$$L = S^* \phi\Big(\frac{S}{S^*}\Big) + \frac{I^*}{\gamma e^{-d\tau}}\,\phi\Big(\frac{I}{I^*}\Big) + \beta S^* I^* \int_{t-\tau}^{t} \phi\Big(\frac{S(\theta) I(\theta)}{S^* I^*}\Big) d\theta$$

has derivative

$$L' = -\frac{d (S - S^*)^2}{S} + \beta S^* I^* \Big[\Big(1 - \frac{S^*}{S} + \ln\frac{S^*}{S}\Big) + \Big(1 - \frac{S_\tau I_\tau}{S^* I} + \ln\frac{S_\tau I_\tau}{S^* I}\Big)\Big] \le 0,$$

where $S_\tau = S(t - \tau)$, $I_\tau = I(t - \tau)$ and $1 - x + \ln x \le 0$. Equality forces $S = S^*$ and then $I = I^*$ on the invariant set, so LaSalle's principle gives convergence to $P^*$. The source proves item 2 with a variant of this functional built from the same Volterra terms (with $S(t-\tau)$ in the first term) and the same two inequalities.

## Sources

- S. Çakan, "Dynamic analysis of a mathematical model with health care capacity for COVID-19 pandemic", *Chaos, Solitons & Fractals* 139 (2020) 110033, Section 2.5, Theorems 3–4 and Eqs. (10)–(12); the functional displayed for item 2 is the standard delayed-SIR form written out here. <https://doi.org/10.1016/j.chaos.2020.110033> (PMC7305938).
