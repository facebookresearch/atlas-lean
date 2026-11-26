# Asymptotics and final-size bound for the SEIR model with suppression and vaccination

**Model.** For population fractions $s, e, i, r$ with $s + e + i + r = 1$, baseline transmission $\beta$, incubation rate $\sigma$ and recovery rate $\gamma$, consider

$$\dot s = -(\beta - h(t)) s i - u(t) s, \qquad \dot e = (\beta - h(t)) s i - \sigma e, \qquad \dot i = \sigma e - \gamma i, \qquad \dot r = \gamma i + u(t) s,$$

where the suppression effort (non-pharmaceutical interventions) $h(t) \in [0, h_{\max}]$ with $0 \le h_{\max} < \beta$ lowers the transmission rate, and the vaccination rate $u(t) \in [0, u_{\max}]$ vanishes before an operational delay $t_{\mathrm{delay}}$. Assume $s_0 > 0$, $i_0 > 0$ and measurable controls.

**Proposition.**

1. There is a unique global Lipschitz solution, which stays in the simplex.
2. The non-recovered mass satisfies $s(t) + e(t) + i(t) - (s_0 + e_0 + i_0) = -\int_0^t \bigl[u(\tau) s(\tau) + \gamma i(\tau)\bigr] d\tau$.
3. $s$ is strictly decreasing, $i(t) \to 0$, $e(t) \to 0$, and $s_\infty = \lim_{t\to\infty} s(t) \in [0, s_0]$ exists.
4. (Maximal suppression, no vaccination) If $h \equiv h_{\max}$ and $u \equiv 0$, then with $\tilde\beta = \beta - h_{\max}$ and $X_0 = s_0 + e_0 + i_0$,

$$\ln \frac{s_\infty}{s_0} = -\frac{\tilde\beta}{\gamma}\bigl(X_0 - s_\infty\bigr).$$

5. (General vaccination) For any vaccination schedule $u$ and suppression bounded by $h_{\max}$,

$$s_\infty \le s_0 \exp\Bigl(-\int_0^\infty \bigl[(\beta - h_{\max}) i(\tau) + u(\tau)\bigr] d\tau\Bigr).$$

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Summing the first three equations gives the integral identity, so $\int_0^\infty (us + \gamma i)\, dt \le X_0$ and $i$ is integrable; since $i$ is Lipschitz, Barbalat's lemma forces $i \to 0$, and then $e \to 0$ from the $e$ equation. Dividing the $s$ equation by $s$ gives $\frac{d}{dt}\ln s = -(\beta - h) i - u \le -(\beta - h_{\max}) i - u$, and integration yields the bound on $s_\infty$. When $h \equiv h_{\max}$ and $u \equiv 0$ the inequality is an equality, and combining it with $\gamma \int_0^\infty i\, dt = X_0 - s_\infty$ gives the Kermack–McKendrick-type final-size equation with the suppressed transmission rate.

## Sources

- Behrooz Moosavi Ramezanzadeh, "Optimal Control of an Epidemic with Intervention Design", arXiv (2025). Theorem 2.2, Corollary 2.5, Corollary 2.6, Proposition 2.7, Corollary 2.8. <https://doi.org/10.48550/arXiv.2503.22928>
