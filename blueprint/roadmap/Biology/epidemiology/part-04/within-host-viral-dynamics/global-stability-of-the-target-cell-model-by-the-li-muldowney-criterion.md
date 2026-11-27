# Global stability of the target-cell model by the Li–Muldowney criterion

**Model.** Uninfected target cells $E$ (pulmonary epithelial cells), infected cells $E^*$ and free virus $v$ satisfy

$$\dot E = d_E(E_0 - E) - \beta E v, \qquad \dot E^* = \beta E v - d_{E^*} E^*, \qquad \dot v = \pi_v E^* - d_v v,$$

with regeneration toward the uninfected level $E_0 > 0$ at rate $d_E$, infection rate $\beta$, infected-cell death rate $d_{E^*}$, virion production $\pi_v$ and clearance $d_v$. The nonnegative orthant is invariant and solutions enter the bounded set $\{E + E^* \le d_E E_0/\delta,\ v \le K\}$, $\delta = \min\{d_E, d_{E^*}\}$.

**Reproduction number and equilibria.** By the next-generation method,

$$\chi_0 = \frac{\pi_v \beta E_0}{d_{E^*} d_v}.$$

The uninfected equilibrium is $S_1 = (E_0, 0, 0)$; for $\chi_0 > 1$ there is a unique infected equilibrium

$$S_2 = \Big(\frac{E_0}{\chi_0},\ \frac{d_v d_E}{\beta\pi_v}(\chi_0 - 1),\ \frac{d_E}{\beta}(\chi_0 - 1)\Big).$$

**Theorem.**

1. If $\chi_0 \le 1$, $S_1$ is globally asymptotically stable: $L = \frac{\pi_v}{d_{E^*}}E^* + v$ satisfies $\dot L = d_v v\big(\frac{\pi_v\beta E}{d_{E^*}d_v} - 1\big) \le d_v v(\chi_0 - 1) \le 0$ on the region where $E \le E_0$, and LaSalle's invariance principle gives convergence to $S_1$. If $\chi_0 > 1$, $S_1$ is unstable.
2. If $\chi_0 > 1$, $S_2$ is globally asymptotically stable in the interior of the feasible region.

Part 2 follows from the [Li–Muldowney second-compound criterion](../../part-01/geometric-approach-to-global-stability/li-muldowney-second-compound-criterion.md) on the interior of the feasible region, where $S_2$ is the unique equilibrium. For the target-cell model, with $B$ and the Lozinskiĭ measure $\mu$ as in the criterion, $A = \mathrm{diag}(1, E^*/v, E^*/v)$ and the measure induced by a mixed vector norm give $\mu(B) \le \dot E^*/E^* - \delta$, so $\frac1t\int_0^t \mu(B)\,ds \le o(1) + \frac1t\ln\frac{E^*(t)}{E^*(\bar t)} - \frac{t - \bar t}{t}\delta \to -\delta < 0$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Li–Muldowney second-compound criterion](../../part-01/geometric-approach-to-global-stability/li-muldowney-second-compound-criterion.md)
- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

The model is the standard basic viral dynamics model with recruitment written as $d_E E_0$, so $\chi_0$ is the product of infections per virion, $\beta E_0/d_v$, and virions per infected cell, $\pi_v/d_{E^*}$. Local stability follows from Routh–Hurwitz: at $S_1$ the cubic has coefficients $a_3 = d_E d_{E^*} d_v(1 - \chi_0)$ and $a_1 a_2 - a_3 > 0$ when $\chi_0 < 1$; at $S_2$ all coefficients and $b_1 b_2 - b_3$ are positive. The compound-matrix method replaces a global Lyapunov function for the endemic state: $\bar q_2 < 0$ rules out periodic orbits, homoclinic loops and heteroclinic cycles (a Bendixson-type criterion in higher dimension), and uniform persistence plus uniqueness of the interior equilibrium then gives global stability. The weights $E^*/v$ in $A$ are chosen so that the off-diagonal blocks of $B$ cancel against logarithmic derivatives of the model variables.

## Sources

- B. J. Nath, K. Dehingia, V. N. Mishra, Y.-M. Chu, H. K. Sarmah, "Mathematical analysis of a within-host model of SARS-CoV-2", Advances in Difference Equations 2021 (2021) 113, Sections 2–6 (model (2.1), Lemmas 1–2, $\chi_0$ and steady states, Theorems 1–4 with Lyapunov functional (6.1) and compound-matrix computation (6.3)–(6.6)), <https://doi.org/10.1186/s13662-021-03276-1>.
- M. Y. Li, J. S. Muldowney, "A geometric approach to global-stability problems", SIAM Journal on Mathematical Analysis 27 (1996) 1070–1083, <https://doi.org/10.1137/S0036141094266449>.
