# Modular response analysis of drug responses in kinase cascades

**Local and global responses.** Consider a signaling network relaxing to a stable steady state, a drug at dose $I$ inhibiting a primary target kinase $X_1$, and pathway output $T$. The *global* (systems-level) response is $R_{TI} = dT/dI$ at the system steady state. *Local* responses, or connection coefficients, are partial derivatives computed with only one module relaxed: $r_{X_1 I} = \partial X_1 / \partial I < 0$ (drug inhibits the target), $r_{X_j X_{j-1}} = \partial X_j / \partial X_{j-1}$ for cascade tiers, and $r_{X_1 T} = \partial X_1 / \partial T$ for feedback from the output.

**Feedback cascade.** For a linear cascade $X_1 \to X_2 \to \dots \to X_N \to T$ with feedback from $T$ to $X_1$,

$$R_{TI} = \frac{r_{X_1 I}\, P}{1 - r_{X_1 T}\, P}, \qquad P = r_{X_2 X_1}\, r_{X_3 X_2} \cdots r_{T X_N} > 0 .$$

With negative feedback ($r_{X_1 T} < 0$) the denominator exceeds one, so $R_{TI} < 0$ and $|R_{TI}| < |r_{X_1 I}|\,P$: inhibition is attenuated but the response never changes sign, so loss of negative feedback cannot fully restore steady-state output. (Strong feedback with delay can instead destabilize the steady state and cause oscillations.) A negative-feedback regulator synthesized in proportion to the output without degradation, $\dot{[NR]} = k_s [\mathrm{MAPK}]$, acts as an integrator but has no steady state, and any degradation breaks the integral action.

**Incoherent feedforward.** If $X_1$ reaches $T$ through an activating route with product $P_X > 0$ and an inhibiting route with product $P_Y < 0$, then

$$R_{TI} = r_{X_1 I}\,(P_X + P_Y),$$

which is positive (paradoxical activation by an inhibitor) whenever the inhibitory route dominates, $P_X + P_Y < 0$; as the dose changes the sign of $P_X + P_Y$ can change, giving dose windows of reactivation. Complete reactivation therefore requires at least two connection routes of opposite sign, which feedback loops alone cannot form.

**Integral feedback with moiety conservation.** With an antithetic controller $\dot Y_1 = \mu - \eta Y_1 Y_2$, $\dot Y_2 = \theta T - \eta Y_1 Y_2$, one has $Y_1 - Y_2 = \int (\mu - \theta T)\, dt$, so the only possible steady state has $T = \mu/\theta$. But if the total amount $X_1^{\mathrm{tot}}$ of the drug target is conserved, inhibitor-free active target satisfies $X_1 \le X_1^{\mathrm{tot}}/(1 + I/K_d)$; with steady-state output $T = F(X_1)$, large enough $I$ drives $T$ near $F(0) \ne \mu/\theta$, so the set-point becomes inaccessible and perfect reactivation fails.

## Depends on

- [Kinetic pairing and the RPA polynomial of reaction networks](../../integral-feedback-and-perfect-adaptation/kinetic-pairing-and-the-rpa-polynomial-of-reaction-networks.md)

## Expansion

Linearizing around the steady state, a small dose change $dI$ moves $X_1$ by $r_{X_1 I}\,dI + r_{X_1 T}\,dT$ and propagates down the cascade as $dT = P\, dX_1$; eliminating $dX_1$ gives the feedback formula, the classical result that proportional feedback scales a response by $1/(1 - \text{loop gain})$. With two parallel routes, $dT = (P_X + P_Y)\, dX_1$ and $dX_1 = r_{X_1 I}\, dI$, which gives the feedforward formula. Because connection coefficients are local quantities, these formulas hold for any mechanistic details inside the modules, and ultrasensitive cascades ($P > 1$) can make the residual inhibition small without ever cancelling it. The integral-control argument shows the internal model principle's set-point is only reachable if it lies in the range of the saturating transfer function from target to output; moiety conservation bounds that range.

## Sources

- B. N. Kholodenko, N. Rauch, W. Kolch, O. S. Rukhlenko, "A systematic analysis of signaling reactivation and drug resistance", Cell Reports (2021), Results, "Pathway response to the inhibition of the first-tier kinase" (Equations 1–5), "Signaling reactivation brought about by pathway crosstalk" (Equation 7), and STAR Methods (negative-feedback regulator, Equations 7.1–7.2; antithetic integral feedback with moiety conservation, Equations 7.3–7.5). <https://doi.org/10.1016/j.celrep.2021.109157> (PMC8202068).
