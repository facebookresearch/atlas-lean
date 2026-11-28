# Peak-minimizing intervention in the SIR model under an L1 budget

**Problem.** In the SIR model with an intervention $u(t)\in[0,1]$ that scales down transmission,

$$\dot S=-\beta SI(1-u),\qquad \dot I=\beta SI(1-u)-\gamma I ,$$

with $\mathcal R_0=\beta/\gamma>1$, herd-immunity threshold $S_h=\gamma/\beta$ and initial state $(S_0,I_0)$ with $S_0>0$, $I_0>0$, $S_0+I_0\le1$ and $S_0>S_h$, minimize the epidemic peak $\max_{t\ge0}I(t)$ over measurable controls with total budget

$$\int_0^\infty u(t)\,dt\le Q .$$

Without intervention the peak is $I_h=I_0+S_0-S_h-S_h\log(S_0/S_h)$, attained when $S=S_h$.

**NSN feedback.** For a target $\bar I\in[I_0,I_h]$, the "null–singular–null" feedback is

$$\psi_{\bar I}(S,I)=\begin{cases}1-\dfrac{S_h}{S},& I=\bar I\ \text{and}\ S>S_h,\\[1mm] 0,&\text{otherwise}:\end{cases}$$

do nothing until $I$ reaches $\bar I$, then hold $I\equiv\bar I$ (a singular arc on which the effective reproduction number is exactly one) until $S$ drops to $S_h$, then stop.

**Theorem.**

1. Under the NSN feedback $\max_tI(t)=\bar I$, the control never exceeds $u_{\max}(\bar I)=1-S_h/\bar S<1$, where $\bar S$ solves $\bar S-S_h\log\bar S=S_0+I_0-S_h\log S_0-\bar I$, and the control switches off continuously at the end of the singular arc.
2. Its total cost is

$$\mathcal L(\bar I)=\int_0^\infty u\,dt=\frac{I_h-\bar I}{\beta S_h\bar I}.$$

3. *(Optimality.)* The NSN feedback is optimal, and the minimal achievable peak is

$$\bar I^{\rm opt}=\begin{cases}\dfrac{I_h}{Q\beta S_h+1},& Q<\dfrac{I_h-I_0}{\beta S_hI_0},\\[2mm] I_0,& Q\ge\dfrac{I_h-I_0}{\beta S_hI_0},\end{cases}$$

the budget being exactly exhausted in the first case.

So the optimal policy spends the whole budget on a single holding phase that keeps prevalence flat at the lowest level the budget allows, starting as late as possible and ending exactly at herd immunity; no intervention outside that arc is useful.

## Expansion

On the arc $I\equiv\bar I$ one needs $\beta S(1-u)=\gamma$, i.e. $u=1-S_h/S$, and $\dot S=-\gamma\bar I$, so $S$ decreases linearly from $\bar S$ to $S_h$; integrating $u\,dt=(1-S_h/S)\,dS/(-\gamma\bar I)$ and using the first integral $S+I-S_h\log S=\text{const}$ of the uncontrolled phase gives $\mathcal L(\bar I)$ in closed form. Since $\mathcal L$ is decreasing in $\bar I$, the budget constraint $\mathcal L(\bar I)\le Q$ gives the smallest admissible target $I_h/(Q\beta S_h+1)$. Optimality follows by comparing any admissible control with the NSN control along the invariant $S+I-S_h\log S$: lowering the peak below $\bar I$ requires keeping $I\le\bar I$ until $S\le S_h$, and the NSN arc reaches $S_h$ with the least $L^1$ effort among such controls.

## Sources

- Emilio Molina, Alain Rapaport, "An optimal feedback control that minimizes the epidemic peak in the SIR model under a budget constraint", Automatica 146 (2022), 110596, <https://doi.org/10.1016/j.automatica.2022.110596>. Published version of arXiv:2203.05800, cited next; locators there refer to the arXiv version.
- E. Molina, A. Rapaport, "An optimal feedback control that minimizes the epidemic peak in the SIR model under a budget constraint", arXiv:2203.05800 (2022), Section 2 (model, assumptions, definition of the NSN feedback), Lemma 1, Proposition 1, Corollary 1 and Proposition 2. <https://doi.org/10.48550/arXiv.2203.05800>
