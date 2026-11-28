# Sensitive–resistant Hahnfeldt model under chemotherapy and anti-angiogenic therapy

**Model.** Drug-sensitive and drug-resistant tumour volumes $N_1, N_2$ and the vascular carrying capacity $K$ evolve as

$$\begin{aligned}
\dot N_1 &= -\lambda_1 N_1 \ln\frac{N_1 + N_2}{K} - \tau_1 N_1 + \tau_2 N_2 - \beta_1 N_1 u(t),\\
\dot N_2 &= -\lambda_2 N_2 \ln\frac{N_1 + N_2}{K} + \tau_1 N_1 - \tau_2 N_2,\\
\dot K &= -\mu K + b(N_1 + N_2) - d (N_1 + N_2)^{2/3} K - \beta K u(t) - \gamma K v(t),
\end{aligned}$$

with Gompertz proliferation rates $\lambda_1, \lambda_2$, mutation rates $\tau_1$ (to resistance) and $\tau_2$ (back to sensitivity), log-kill chemotherapy of sensitive cells at rate $\beta_1 u(t)$, vascular stimulation $b$ and inhibition $d$ by the tumour (Hahnfeldt et al.), endothelial death $\mu$, and vascular sensitivities $\beta, \gamma$ to the chemotherapeutic dose $u(t)$ and anti-angiogenic dose $v(t)$. For bounded continuous doses, $\{N_1, N_2, K > 0\}$ is positively invariant and solutions exist for all $t \ge 0$.

**Steady state under constant doses** $u, v$. Let $A = \lambda_1\tau_1$, $B = \lambda_2\tau_1 - \lambda_1\tau_2 + \beta_1\lambda_2 u$, $C = -\lambda_2\tau_2$, $\Delta = B^2 - 4AC > 0$, and

$$R = \frac{\sqrt\Delta - B}{2A} > 0, \qquad \alpha = \frac{\tau_1 R - \tau_2}{\lambda_2} .$$

System has exactly one positive steady state, with $\bar N_1/\bar N_2 = R$, $\bar N_1 + \bar N_2 = \bar K e^{\alpha}$ and

$$\bar K = \frac{\big(b e^{\alpha} - \mu - \beta u - \gamma v\big)^{3/2}}{d^{3/2} e^{\alpha}},$$

which exists iff $b e^{\alpha} - \mu - \beta u - \gamma v > 0$. It is locally stable if

$$b\big(\bar K e^{\alpha} - 1\big) + \tfrac{2}{3}\, d\, \bar K^{2/3} e^{-\alpha/3} > 0$$

and unstable under the reverse inequality; in particular $b e^{\alpha} - \mu - \beta u - \gamma v > d$ guarantees both existence and stability.

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

At a positive steady state, adding the tumour equations gives $\ln\frac{N_1+N_2}{K} = -\beta_1 u N_1/(\lambda_1 N_1 + \lambda_2 N_2)$, and substituting into the $N_2$ equation yields $\beta_1\lambda_2 u N_1 N_2 + (\lambda_1 N_1 + \lambda_2 N_2)(\tau_1 N_1 - \tau_2 N_2) = 0$, a quadratic $Ax^2 + Bx + C = 0$ in $x = N_1/N_2$; since $AC < 0$ it has exactly one positive root $R$. The $N_2$ equation then fixes $\ln\frac{N_1 + N_2}{K} = \alpha$, and the $K$ equation, with $N_1 + N_2 = K e^\alpha$, gives $b e^\alpha - \mu - \beta u - \gamma v = d K^{2/3} e^{2\alpha/3}$. Stability follows from Routh–Hurwitz applied to the cubic characteristic polynomial: the leading coefficient conditions hold automatically, the constant term has the sign of the displayed inequality, and the steady-state relation $b e^\alpha > \tfrac23 d (\bar K e^\alpha)^{2/3}$ yields $a_1 a_2 > a_0$. Since resistant cells are untouched by $u$, higher chemotherapy doses shift the steady-state composition toward resistance ($R$ decreases in $u$), which motivates comparing continuous, metronomic and anti-angiogenic-first schedules.

## Sources

- M. Bodzioch, P. Bajger, U. Foryś, "Angiogenesis and chemotherapy resistance: optimizing chemotherapy scheduling using mathematical modeling", Journal of Cancer Research and Clinical Oncology 147 (2021) 2281–2299, Model (System (1), Table 1) and Appendix (Propositions 1–5 with proofs, equations (2)–(8)), <https://doi.org/10.1007/s00432-021-03657-9>.
- P. Hahnfeldt, D. Panigrahy, J. Folkman, L. Hlatky, "Tumor development under angiogenic signaling: a dynamical theory of tumor growth, treatment response, and postvascular dormancy", Cancer Research 59 (1999) 4770–4775.
