# Periodic solutions under cyclic chemotherapy in the acid-mediated invasion model

**Setting.** Take the [acid-mediated tumour invasion model with chemotherapy](acid-mediated-tumour-invasion-model-with-chemotherapy.md) with a $\rho$-periodic infusion $i(t+\rho) = i(t) \ge 0$ of mean $\frac1\rho\int_0^\rho i = 1$ (e.g. a periodic boxcar for cyclic intravenous dosing). Periodic solutions replace steady states. When normal tissue is absent ($u_1 \equiv 0$, which also decouples the acid), the tumour–drug dynamics reduce to

$$x_1' = \beta_2x_1(1 - x_1 - \delta_2x_2), \qquad x_2' = \beta_4\big(i(t) - x_2 - \delta_4x_1x_2\big).$$

**Theorem (reduced system).** If $0 < \delta_2 < 1$, the reduced system has a unique solution with $\mathbf{x}(t+\rho) = \mathbf{x}(t) > 0$ for all $t \ge 0$, and this periodic solution is asymptotically stable (both characteristic multipliers have modulus less than $1$).

**Theorem (coexistence).** Let $\hat u_{2+} = \big(\delta_4 - 1 + \sqrt{(1-\delta_4)^2 + 4\delta_4(1-\delta_2)}\big)/(2\delta_4)$. If

$$\delta_2 < 1, \qquad 1 - (\alpha_1 + \delta_1)\hat u_{2+} > 0, \qquad 1 < \alpha_1(1 - \delta_2), \qquad 1 - \delta_2 < \alpha_2$$

(or the same with both of the last two inequalities reversed), then the full four-dimensional system has a strictly positive $\rho$-periodic solution: normal and tumour tissue coexist in a treatment-locked cycle.

The other periodic solutions are the trivial one $(0,0,0,w(t))$, the tumour-free one $(1,0,0,w(t))$ and the normal-tissue-free one $(0, x_1(t), u_3(t), x_2(t))$, where $w$ is the unique periodic solution of $w' = \beta_4(i(t) - w)$.

## Expansion

Existence for the reduced system uses monotone comparison: with $M = \mathrm{diag}(1,-1)$ the system is cooperative, sandwiched between two explicitly solvable systems (drug without consumption; tumour without drug kill), and the Poincaré map sends the order interval between their periodic orbits into itself, so Brouwer's theorem gives a periodic orbit. Uniqueness follows because two distinct positive periodic orbits would be strictly ordered in $x_1$, contradicting the periodicity of a Lyapunov-type function $V(\mathbf{x})$ whose derivative appears in the implicit quadratic formula for $x_1$. Stability uses a periodic weight $\boldsymbol\xi(t)$ with $\int_0^\rho \frac{d}{dt}\langle\boldsymbol\xi,\mathbf{y}\rangle\,dt < 0$ along the Perron eigenvector of the monodromy matrix, which forces the dominant multiplier below $1$. The same order-interval argument with $M = \mathrm{diag}(1,-1,-1,1)$ yields the coexistence orbit. The threshold $\delta_2 < 1$ matches the constant-infusion case: cycling the dose with the same mean does not by itself change whether the drug alone can clear the tumour.

## Sources

- Andrew B. Holder, Marianito R. Rodrigo, "Model for Acid-Mediated Tumour Invasion with Chemotherapy Intervention I: Homogeneous Populations", arXiv:1412.0748 (2014): Section 4.1 (reduced system: existence, uniqueness, Theorem 4.1; stability and Remark 4.2), Section 4.2 (coexistence periodic solution, Theorem 4.3), Section 4.3 (classification of special periodic solutions). <https://doi.org/10.48550/arXiv.1412.0748>
