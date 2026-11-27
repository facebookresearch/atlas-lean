# Lyapunov function for the normalized SIRS model with disease mortality

**Model.** Let $I(t)$ and $R(t)$ be the infectious and recovered fractions of a population whose size changes according to $\dot N = (g - \delta I)N$, where $g = \theta - \zeta$ is births minus natural deaths and $\delta>0$ is the disease death rate. With transmission rate $\mathcal B$, recovery rate $\gamma$ and waning-immunity rate $\psi$, the normalized SIRS dynamics are

$$
\begin{aligned}
\dot I &= (\mathcal B S + \delta I - \sigma)\, I, \\
\dot R &= \gamma I - \omega R + \delta R I,
\end{aligned}
$$

with $S = 1 - I - R$, $\sigma = g + \gamma + \zeta + \delta$ and $\omega = g + \psi + \zeta$. Disease deaths remove infected individuals from the denominator, which produces the extra terms $\delta I^2$ and $\delta RI$ absent from the model with $\delta = 0$. Assume $\delta<\omega$, $\delta<\gamma$ and $\sigma<\mathcal B$.

**Endemic equilibrium.** The endemic equilibrium $(\hat I_{\mathcal B},\hat R_{\mathcal B})$ is the unique solution in $(0,1]\times[0,1]$ of

$$
\mathcal B - \sigma = \mathcal B(\hat I + \hat R) - \delta\hat I, \qquad 0 = \gamma\hat I - \omega\hat R + \delta\hat R\hat I ,
$$

and it satisfies $\hat I_{\mathcal B} + \hat R_{\mathcal B}\le 1$. Explicitly,

$$
\hat I_{\mathcal B} = \frac{b_{\mathcal B} - \sqrt{\Delta}}{2\delta(\mathcal B - \delta)}, \qquad
\hat R_{\mathcal B} = \Bigl(1 - \frac{\sigma}{\mathcal B}\Bigr) - \Bigl(1 - \frac{\delta}{\mathcal B}\Bigr)\hat I_{\mathcal B},
$$

where $b_{\mathcal B} = \gamma\mathcal B + \omega(\mathcal B - \delta) + \delta(\mathcal B - \sigma)$ and $\Delta = b_{\mathcal B}^2 - 4\delta\omega(\mathcal B - \delta)(\mathcal B - \sigma)$.

**Lyapunov function.** Fix $\mathcal B = \beta^*>\delta$ with endemic equilibrium $(I^*,R^*)$, and let $a = \beta^*/(\gamma + \delta R^*)$. The function

$$
\mathcal V(I,R) = (I - I^*) + I^*\ln\frac{I^*}{I} + \frac{a}{2}(R - R^*)^2
$$

satisfies, along solutions,

$$
\frac{d}{dt}\mathcal V(I,R) = -(\beta^* - \delta)(I - I^*)^2 - a(\omega - \delta I)(R - R^*)^2 .
$$

Since $\delta<\omega$, this is negative definite on $(0,1]\times[0,1]$, so the endemic equilibrium is globally asymptotically stable there.

## Expansion

Using the equilibrium relations, rewrite the system as $\dot I = \bigl(\beta^*(R^* - R) + (\beta^* - \delta)(I^* - I)\bigr)I$ and $\dot R = (\gamma + \delta R^*)(I - I^*) - (\omega - \delta I)(R - R^*)$. The Volterra term contributes $(1 - I^*/I)\dot I = (I - I^*)\bigl(\beta^*(R^* - R) + (\beta^* - \delta)(I^* - I)\bigr)$. The quadratic term contributes $a(R - R^*)\dot R$. The weight $a$ is chosen so that the cross terms $\pm\beta^*(I - I^*)(R - R^*)$ cancel exactly, leaving two negative squares. This modifies the O'Regan–Kelly–Korobeinikov–Wake Lyapunov function to account for disease mortality: the self-damping coefficients become $\beta^* - \delta$ and $\omega - \delta I$, hence the requirement that $\delta$ be moderate. The same function, with $(I^*,R^*)$ replaced by the moving target $(\hat I_{\mathcal B},\hat R_{\mathcal B})$, is the epidemic part of the Lyapunov function used for epidemic population games.

## Sources

- Jair Certorio, Nuno C. Martins, Richard J. La, "Epidemic Population Games With Nonnegligible Disease Death Rate", IEEE Control Systems Letters 6 (2022), 3229–3234, <https://doi.org/10.1109/lcsys.2022.3183477>. Published version of arXiv:2204.00953, cited next; locators there refer to the arXiv version.
- Jair Certório, Nuno C. Martins, Richard J. La, "Epidemic Population Games With Nonnegligible Disease Death Rate", arXiv 2022: Section III (modified SIRS model, Assumption 3, the endemic-equilibrium formulas, the Lyapunov function and its derivative) and Remark 3. <https://doi.org/10.48550/arXiv.2204.00953>
