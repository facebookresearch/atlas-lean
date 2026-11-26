# Frequency-induced tipping criterion

**Forced model.** In the [threshold predator-prey system](equilibria-and-sliding-dynamics-of-the-threshold-predator-prey-system.md) replace the prey growth rate $r$ by the periodic rate

$$\rho(t) = r_0 + A \sin\Big(\frac{2\pi t}{\tau} + \phi\Big), \qquad 0 \le A < r_0,$$

with mean $r_0$, amplitude $A$, forcing period $\tau$ and phase $\phi$, so that $\rho(t) > 0$. Write $(N_\tau(t), P_\tau(t))$ for the solution with forcing period $\tau$ started in the coexistence region $R_1 = \{N > N_a, P > P_a\}$, near the coexistence state $E_2$, which in the unforced system is a stable focus with natural period $\tau_n = 2\pi/\omega$.

**Threshold-reaching periods.** Define

$$\mathcal T_N(A) = \Big\{\tau > 0 : \min_{t \ge 0} N_\tau(t) \le N_a\Big\}, \qquad \mathcal T_P(A) = \Big\{\tau > 0 : \min_{t \ge 0} P_\tau(t) \le P_a\Big\},$$

computed for the smooth coexistence dynamics.

**Theorem 1 (frequency-induced tipping criterion).** Assume $\rho(t) > 0$ for all $t$ and $(N_0, P_0) \in R_1$. A necessary condition for frequency-induced tipping is the existence of $\tau_{\mathrm{tip}} \in \mathcal T_N(A) \cup \mathcal T_P(A)$. Let

$$t_c = \inf\Big\{t > 0 : \Big(N(t) = N_a \text{ and } P(t) > \tfrac{\rho(t)}{a}\big(1 - \tfrac{N_a}{K}\big)\Big) \text{ or } \Big(P(t) = P_a \text{ and } N_a < N(t) < \tfrac{m}{ab}\Big)\Big\}$$

be the first *admissible* crossing time. If $t_c < \infty$, frequency-induced tipping occurs, and its outcome is decided by the first admissible crossing:

- if $N(t_c) = N_a$ and $P(t_c) > \frac{\rho(t_c)}{a}(1 - \frac{N_a}{K})$, the trajectory enters $R_2$ and tips to extinction $E_0$;
- if $P(t_c) = P_a$ and $N_a < N(t_c) < \frac{m}{ab}$, it enters $R_4$ and tips to the prey-only state $E_1$.

Accordingly, $\tau \notin \mathcal T_N \cup \mathcal T_P$ keeps coexistence; $\tau \in \mathcal T_N \setminus \mathcal T_P$ can tip to $E_0$; $\tau \in \mathcal T_P \setminus \mathcal T_N$ tips to $E_1$; and $\tau \in \mathcal T_N \cap \mathcal T_P$ tips to whichever state the first admissible crossing selects.

## Expansion

The forcing amplitude can be small enough that every frozen system $r \in [r_0 - A, r_0 + A]$ still has a stable coexistence focus inside $R_1$, so neither bifurcation-induced nor noise-induced tipping is involved. Tipping arises because forcing near the natural period resonates with the damped oscillations around $E_2$ and amplifies them until a threshold is hit, which makes $\mathcal T_N(A)$ and $\mathcal T_P(A)$ intervals around $\tau_n$ (numerically about $[7.62, 12.05]$ and $[8.60, 12.73]$ for $A = 0.12$ at the baseline parameters). The admissibility conditions encode the sliding analysis: a crossing of $N = N_a$ below the escaping segment, or of $P = P_a$ with $N > m/(ab)$, is not a transversal exit, since those points lie on an escaping sliding segment ($\Sigma_{e,(1,2)}$ or $\Sigma_{e,(4,1)}$), while the stated crossings send the trajectory into $R_2$ or $R_4$, whose smooth fields have $E_0$ or $E_1$ as global attractors. Simulations show the effect persists when the Heaviside switches are smoothed.

## Depends on

- [Equilibria and sliding dynamics of the threshold predator-prey system](equilibria-and-sliding-dynamics-of-the-threshold-predator-prey-system.md)

## Sources

- S. Gao, S. Poloni, H. Wang, M. Lewis, "Frequency-induced Tipping: Resonance-Driven Tipping in a Threshold Predator-Prey System" (2026), Section 2.2 (periodic forcing and natural period), Theorem 1 and the four-case classification following it, Appendix B (smoothed system), <https://doi.org/10.48550/arXiv.2610.39113>.
