# Observer-based predictor for an SIR model with delayed control and measurement

**Problem.** In the normalized SIR model

$$\dot S(t)=-\beta(t-h_1)S(t)I(t),\qquad \dot I(t)=\bigl(\beta(t-h_1)S(t)-\gamma\bigr)I(t),\qquad y(t)=I(t-h_2),$$

the transmission rate $\beta\in[\beta_{\min},\beta_{\max}]$ is set by social distancing that takes effect after a known delay $h_1$, and only the prevalence, delayed by $h_2$, is measured; $\gamma>0$ is known. The goal is to reconstruct and predict $(S,I)$ from the history of $y$, so that a state-feedback distancing policy can be applied without the chattering caused by delays.

**Delay-free observer.** With $x_1=\ln I$ and $x_2=S$ the model becomes $\dot x_1=\beta x_2-\gamma$, $\dot x_2=\beta\rho(x)$ with $\rho(x)=-x_2e^{x_1}$, affine in the state in the first equation. The observer

$$\dot{\breve x}_1=\beta\bigl(\breve x_2+\alpha_1(x_1-\breve x_1)\bigr)-\gamma,\qquad \dot{\breve x}_2=\beta\bigl(\rho(\breve x)+\alpha_2(x_1-\breve x_1)\bigr)$$

has, to first order, time-varying error dynamics $\dot{\tilde x}=\beta(t)A(t)\tilde x$ with

$$A(t)=\begin{pmatrix}-\alpha_1&1\\-\alpha_2-S(t)I(t)&-I(t)\end{pmatrix}.$$

**Proposition.** If

$$\alpha_1>\frac{1}{4\sqrt2},\qquad \alpha_2>\frac{\alpha_1^2+1}{4\sqrt2\,\alpha_1-1},$$

then the linearized error dynamics is quadratically stable: one quadratic Lyapunov function works for all admissible $A(t)$, using $S,I\ge0$ and $S+I\le1$ (so $SI\le\tfrac14$).

**Theorem (predictor).** Rewriting the delayed problem in a new time variable, the predictor error obeys a linear system with a bounded time-varying delay $0<\eta(\tau)\le\bar\eta$ whose matrix ranges over a polytope with vertices $C_1,C_2,C_3$. If there exist $2\times2$ matrices $P>0$, $R\ge0$, $S\ge0$, $P_2,P_3$ satisfying the linear matrix inequalities

$$Q(C_i;P,R,S,P_2,P_3)<0,\qquad i=1,2,3,$$

built from the Lyapunov–Krasovskii functional $V=\varepsilon^\top P\varepsilon+\int_{\tau-\bar\eta}^\tau\varepsilon^\top S\varepsilon+\bar\eta\int_{-\bar\eta}^0\int_{\tau+\theta}^\tau\dot\varepsilon^\top R\dot\varepsilon$ with the descriptor method, then the trivial solution of the predictor error system is asymptotically stable for all delays up to $\bar\eta$, and the predicted states converge to the true states.

## Expansion

The logarithmic change of variables makes the output equation linear in the unknown susceptible fraction, so a Luenberger-type gain $(\alpha_1,\alpha_2)$ suffices; quadratic stability follows by solving the Lyapunov equation for the frozen matrix with $SI$ and $I$ at the extremes of their admissible ranges and checking the cross terms, which gives the explicit gain inequalities. For the delayed problem, a chain of observers (or a time rescaling by $\beta$) turns measurement and input delays into a state delay in the error equation. Differentiating the Lyapunov–Krasovskii functional and applying Jensen's inequality bounds $\dot V$ by a quadratic form in $(\varepsilon,\dot\varepsilon,\varepsilon(\tau-\bar\eta),\varepsilon(\tau-\eta(\tau)))$; adding the descriptor identity through free matrices $P_2,P_3$ gives the LMI, and convexity reduces the polytope to its vertices.

## Sources

- Fernando Castaños, Sabine Mondié, "Observer‐based predictor for a susceptible‐infectious‐recovered model with delays: An optimal‐control case study", International Journal of Robust and Nonlinear Control 31 (2021), 5118–5133, <https://doi.org/10.1002/rnc.5522>. Published version of arXiv:2010.12106, cited next; locators there refer to the arXiv version.
- S. Mondié, F. Castaños, "Observer-based predictor for a SIR model with delays", arXiv:2010.12106 (2020), Section 2 (problem statement), Section 4 (delay-free observer and Proposition 1) and the predictor section (Lemma 1 and Theorem 1). <https://doi.org/10.48550/arXiv.2010.12106>
