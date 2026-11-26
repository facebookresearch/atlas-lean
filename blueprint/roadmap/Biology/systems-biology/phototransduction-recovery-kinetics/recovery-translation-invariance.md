# Recovery translation invariance

Let $F[\Phi, t] \in [0, 1]$ be the fraction of circulating current at time $t \ge 0$ after a flash producing $\Phi$ photoisomerizations at $t = 0$. The family $\{F[\Phi, \cdot]\}$ obeys **recovery translation invariance (RTI)** on an intensity range $[\Phi_0, \Phi_{\max}]$ if there are a time $t_0$ and a function $h$ such that

$$F[s\Phi_0, t] = F[\Phi_0, t - h(s)] \qquad \text{for all } s \ge 1 \text{ with } s\Phi_0 \le \Phi_{\max},\ t \ge t_0,$$

together with complete eventual recovery ($F[\Phi, t] \to 1$ as $t \to \infty$) and $F \ge 0$. In words, scaling a saturating flash by $s$ shifts the recovery to the right by $h(s)$ without changing its shape.

**Lemma.** If the family obeys RTI, then $h(s) = \tau \ln s$ for a constant $\tau$ with units of time.

**Theorem.** A family of recovery traces obeys RTI if and only if

$$F[\Phi, t] = H\big(\Phi\, e^{-t/\tau}\big), \qquad \Phi_0 \le \Phi \le \Phi_{\max},\ t \ge t_0,$$

for a saturation function $H$ with $H(0) = 1$ and $H(x) \to 0$ as $x \to \infty$.

## Expansion

Shifting by $s_1 s_2$ in one step or in two steps gives the same curve, so $h(s_1 s_2) = h(s_1) + h(s_2)$, Cauchy's logarithmic functional equation, whose (regular) solutions on the positive reals are $h(s) = \tau \ln s$. Then $F[\Phi, t]$ depends on $(\Phi, t)$ only through $t - \tau\ln\Phi$, i.e. through $\Phi e^{-t/\tau}$, which defines $H$; conversely such an $F$ satisfies RTI with $h = \tau\ln s$. Biologically, RTI is equivalent to the existence of a transduction intermediate produced in proportion to $\Phi$ and decaying with time constant $\tau$ at long times, followed by an arbitrary saturating nonlinearity; the circulating current itself need not decay with $\tau$.

## Sources

- S. Nikonov, N. Engheta, E. N. Pugh Jr., "Kinetics of recovery of the dark-adapted salamander rod photoresponse", Journal of General Physiology 111(1) (1998) 7–37, Eqs. 1–3, Theorem 1, and Appendix I (Lemma and proof of Theorem 1), <https://doi.org/10.1085/jgp.111.1.7>, PMCID PMC1887775.
