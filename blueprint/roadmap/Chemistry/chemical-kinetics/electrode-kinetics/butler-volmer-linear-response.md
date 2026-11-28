# Linear response of the Butler–Volmer current and the charge-transfer resistance

Near equilibrium the Butler–Volmer current is linear in the overpotential, $j=\eta/R_{\mathrm{ct}}+O(\eta^2)$ with area-specific charge-transfer resistance $R_{\mathrm{ct}}=RT/(nFj_0(\alpha_a+\alpha_c))$.

For the [Butler–Volmer current density](butler-volmer-equation.md) with $j_0,\alpha_a,\alpha_c>0$, $n\ge1$, $T>0$,

$$j'(0)=j_0nf(\alpha_a+\alpha_c)=\frac1{R_{\mathrm{ct}}},\qquad R_{\mathrm{ct}}=\frac{RT}{nFj_0(\alpha_a+\alpha_c)}>0\quad(\Omega\,\mathrm{m}^2),$$

and for every $\eta_0>0$ and $|\eta|\le\eta_0$,

$$\Big|j(\eta)-\frac{\eta}{R_{\mathrm{ct}}}\Big|\le\frac{j_0(nf)^2}{2}\big(\alpha_a^2e^{\alpha_anf\eta_0}+\alpha_c^2e^{\alpha_cnf\eta_0}\big)\,\eta^2 .$$

For a single-step reaction ($\alpha_a+\alpha_c=1$), $R_{\mathrm{ct}}=RT/(nFj_0)$.

## Context

Undergraduate electrochemistry. $R_{\mathrm{ct}}$ is the resistance read from the high-frequency arc of impedance spectra and the small-signal element of equivalent-circuit battery models.

## Depends on

- [Butler–Volmer equation](butler-volmer-equation.md)

## Proof depends on

- [Taylor's theorem with the Lagrange remainder](../../../Analysis/real-functions/differential-calculus/taylor-theorem-with-lagrange-remainder.md)

## Expansion

$j$ is smooth with $j'(\eta)=j_0nf(\alpha_ae^{\alpha_anf\eta}+\alpha_ce^{-\alpha_cnf\eta})$ and $j''(\eta)=j_0(nf)^2(\alpha_a^2e^{\alpha_anf\eta}-\alpha_c^2e^{-\alpha_cnf\eta})$. Taylor's theorem with the Lagrange remainder at order one gives $j(\eta)-j'(0)\eta=\tfrac12j''(\eta')\eta^2$ for some $\eta'$ between $0$ and $\eta$, and $|j''(\eta')|$ is at most the bracket for $|\eta'|\le\eta_0$. Lecture 13 (Sec. 3A) states the linearization and the constant activation resistance; the explicit constant is this bound.

## Sources

- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 13: Butler-Volmer equation, Sec. 3A (linear response, constant resistance of the Faradaic reaction). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec13.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
