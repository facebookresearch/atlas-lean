# Feedback threshold for stability of the Friberg model

**Model.** The semimechanistic model of drug-induced myelosuppression tracks proliferating bone-marrow progenitors $P$, maturing cells in transit compartments $T_1, T_2, T_3$, and circulating blood cells $C$:

$$\dot P = k_{\mathrm{prol}} P \Big(\frac{C^*}{C}\Big)^{\gamma}(1 - E_{\mathrm{drug}}) - k_{tr} P,\quad \dot T_1 = k_{tr}(P - T_1),\quad \dot T_i = k_{tr}(T_{i-1} - T_i)\ (i = 2,3),\quad \dot C = k_{tr} T_3 - k_{\mathrm{circ}} C,$$

with $k_{\mathrm{prol}} = k_{tr} = k_{\mathrm{circ}} = 4/\mathrm{MTT}$ (mean transit time), baseline $C^*$, and feedback exponent $\gamma > 0$: low blood counts boost proliferation through $(C^*/C)^\gamma$. Without drug ($E_{\mathrm{drug}} = 0$) the unique positive equilibrium is homeostasis, $P = T_1 = T_2 = T_3 = C = C^*$.

**Theorem.** The characteristic polynomial of the linearization at homeostasis is

$$\lambda^5 + 4k_{tr}\lambda^4 + 6k_{tr}^2\lambda^3 + 4k_{tr}^3\lambda^2 + k_{tr}^4\lambda + \gamma k_{tr}^5 = \lambda(\lambda + k_{tr})^4 + \gamma k_{tr}^5 .$$

Homeostasis is locally asymptotically stable if and only if $\gamma < \gamma^* \approx 0.5685$, independently of $C^*$ and MTT; at $\gamma = \gamma^*$ a pair of eigenvalues crosses the imaginary axis (a Hopf bifurcation), and for $\gamma > \gamma^*$ perturbations such as drug-induced cytopenia grow into sustained, non-biological oscillations instead of returning to baseline.

## Expansion

Writing $\lambda = k_{tr}\mu$ reduces the characteristic equation to $\mu(1+\mu)^4 = -\gamma$, so stability depends on $\gamma$ alone. An imaginary root $\mu = i\omega$ requires $\arg\big(i\omega(1+i\omega)^4\big) = \pi$, i.e. $\pi/2 + 4\arctan\omega = \pi$, giving $\omega = \tan(\pi/8)$ and

$$\gamma^* = \tan\frac{\pi}{8}\,\sec^4\frac{\pi}{8} = 0.56854\ldots,$$

in agreement with the Routh–Hurwitz computation. The same argument applies to a chain of $n$ transit compartments, where $\lambda(\lambda+k_{tr})^{n+1} + \gamma k_{tr}^{n+2} = 0$ and the threshold $\tan\theta\,\sec^{n+1}\theta$ with $\theta = \pi/(2(n+1))$ decreases with $n$ (it is $2$ for $n=1$), so longer maturation delays destabilize the feedback. Variants that estimate the progenitor pool separately or decouple proliferation from maturation have thresholds depending on $P^*/C^*$ or MTT. In a thrombocytopenia case study, fitted values of $\gamma$ above $\gamma^*$ produced unreliable long-term predictions, so fitted parameters should be checked against the stability region.

## Sources

- C. Fornari, C. Pin, J. W. T. Yates, J. T. Mettetal, T. A. Collins, "Importance of stability analysis when using nonlinear semimechanistic models to describe drug-induced hematotoxicity", CPT: Pharmacometrics & Systems Pharmacology (2020), Methods (Eqs 1–8, Table 1, Models A–D) and Results (stability threshold $\gamma^* = 0.5685\ldots$), <https://doi.org/10.1002/psp4.12514>, PMCID PMC7499189.
