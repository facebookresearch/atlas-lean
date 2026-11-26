# Cumulative dose ordering and delayed slope reversal in a feedback-coupled incoherent feedforward loop

**Model.** In dimensionless form, an input (dose) $u \in [u_-, u_+] \subset (0,\infty)$ drives an activator $x$ and an output $y$ that $x$ also represses, with feedback branches $e$ through slow variables $z_e$:
$$\dot x = u + \sum_e \alpha_e a_e\,\phi_e(z_e) - x, \qquad \dot z_e = \kappa_e(x - z_e), \qquad \dot y = \frac{u + \sum_e\alpha_e b_e\,\phi_e(z_e)}{x} - y,$$
with $0 \le b_e \le a_e$, $\kappa_e > 0$, $0 \le \phi_e \le M_e$, $0 \le \phi_e' \le L_e$, and fixed initial values $x_0 > 0$, $z_{e0}, y_0 \ge 0$. At $\alpha = 0$ the $(x,y)$ subsystem is the canonical incoherent feedforward loop (IFFL), whose cumulative output $C_T = \int_0^T y\,dt$ increases with $u$. Let $x_L(t) = u_- + (x_0 - u_-)e^{-t}$, $\overline x = \max\{x_0, u_+ + \sum_e a_eM_e\}$, $A_T = [1 - (1+T)e^{-T}]/\overline x$, and let $(\bar p, \bar s_e)$ solve $\dot{\bar p} = 1 - \bar p + \sum_e a_eL_e\bar s_e$, $\dot{\bar s}_e = \kappa_e(\bar p - \bar s_e)$ from zero.

**Theorem (ordering under nonlinear feedback).** Uniformly over the dose and coupling ranges,
$$\partial_u C_T \;\ge\; A_T - \sum_e \alpha_e B_{e,T}, \qquad B_{e,T} = (a_e - b_e)L_e\int_0^T\big(1 - e^{-(T-t)}\big)\frac{\bar s_e}{x_L}\,dt,$$
and with $\underline x_T = \min\{x_0, x_L(T)\}$, $\gamma = \max\{0, \sum_e a_eL_e - 1\}$,
$$B_{e,T} \le \frac{(a_e - b_e)L_e\kappa_e e^{\gamma T}T^4}{24\,\underline x_T}.$$
Since $A_T \sim T^2/(2\overline x)$ while $B_{e,T} = O(T^4)$ as $T \to 0$, the cumulative output is increasing in dose on an initial time window, and on all of $[0,T]$ whenever the bound stays positive. Matched branches ($b_e = a_e$) never break ordering.

**Theorem (first loss under weak mismatch).** With one branch, $a = \epsilon$, $b = (1-\eta)\epsilon$, $\alpha = 1$, $\phi(z) = z^2/(1+z^2)$, $0 < \epsilon < 1$, the equilibrium is $x = z = \chi$ with $u = \chi - \epsilon\phi(\chi)$. Fix $\epsilon$, $\kappa > 0$, a dose with $0 < \chi < 1$, and dose-independent initial values. For small mismatch $\eta > 0$, $\partial_uC_T$ has a unique positive zero, the first time the ordering is lost, and
$$T_{\mathrm{loss}}(\eta) = \frac{(1 + \chi^2)^2}{\epsilon\,\eta\,\chi\,(1 - \chi^2)} + O(1) \qquad (\eta \to 0).$$

## Depends on


## Expansion

Differentiating along the solution, $\partial_uC_T$ splits into the direct IFFL contribution, a shared-production term that is positive when the activator also feeds the output's production, and feedback terms proportional to the branch mismatch $a_e - b_e$. The sensitivities obey a linear system whose coefficient matrix is Metzler, so comparison with the explicit majorant $(\bar p, \bar s_e)$ bounds the adverse terms; their small-time order $T^4$ against the $T^2$ direct term gives early ordering. Under weak mismatch, the adverse feedback contribution accumulates at rate $O(\eta)$ near equilibrium while the favorable one saturates, so they balance only after time $\propto 1/\eta$; the leading coefficient comes from linearizing at $x = z = \chi$ with $\phi'(\chi) = 2\chi/(1+\chi^2)^2$.

## Sources

- I. Janković, F. Calandra, G. Perrino and V. Siciliano, "Feedback and Resource Competition in Incoherent Feedforward Loops: When Is Cumulative Dose Ordering Preserved?", arXiv:2611.22710 (2026), Lemma 1, Theorems 1–3 and Corollary 1, <https://doi.org/10.48550/arXiv.2611.22710>.
