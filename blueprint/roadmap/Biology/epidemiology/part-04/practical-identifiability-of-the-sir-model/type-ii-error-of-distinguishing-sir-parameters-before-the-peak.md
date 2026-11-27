# Type II error of distinguishing SIR parameters before the peak

**Model.** The SIR proportions satisfy $\dot s = -\beta i s$, $\dot i = \beta i s - \gamma i$, $\dot r = \gamma i$ with $\theta = (\beta, \gamma)$, population size $N$, initial infected fraction $i_0$ and early growth rate $\delta = \beta - \gamma$. Daily new infections are $\Delta_t = N(s_{t-1} - s_t)$, and observations before the peak are

$$Y_t = p\,\Delta_t + \xi_t, \qquad \xi_t \sim \mathcal{N}(0, \sigma_t^2) \text{ independent}, \qquad t = 1, \dots, T,$$

with reporting probability $p$.

**Early-phase approximation.** While $s \approx 1$, $i_t \approx i_0 e^{\delta t}$ and

$$\Delta_t(\theta) \approx N i_0\, \frac{\beta\,(1 - e^{-\delta})}{\delta}\, e^{\delta t}.$$

Among perturbations $\theta_\epsilon(\omega) = \theta + \epsilon(\cos\omega, \sin\omega)$ of fixed size $\epsilon$, the directions $\omega = \pi/4$ and $5\pi/4$ point along the line $\beta - \gamma = \text{const}$ and leave $\delta$ unchanged, so they change only the prefactor of $\Delta_t$.

**Approximation (type II error).** For the most powerful level-$\alpha$ test of $H_0 : \theta = \theta_0$ against $H_1 : \theta = \theta_\epsilon(\omega)$ (the likelihood ratio test, by the Neyman–Pearson lemma), the type II error is $E_2(\omega) = 1 - \Phi\big(\Phi^{-1}(\alpha) + d(\omega)\big)$ with $d(\omega)^2 = \sum_t p^2\big(\Delta_t(\theta_\epsilon) - \Delta_t(\theta_0)\big)^2/\sigma_t^2$. Using the early-phase approximation, with $f(\omega) = \cos\omega - \sin\omega$,

$$E_2(\omega) \approx 1 - \Phi\!\left(\Phi^{-1}(\alpha) + p N i_0 \sqrt{\sum_{t=1}^{T} \frac{e^{2\delta t}}{\sigma_t^2}\Big((\beta + \epsilon\cos\omega)\, e^{\epsilon t f(\omega)} - \beta\Big)^2}\right),$$

and $E_2(\pi/4) \le \sup_\omega E_2(\omega) \le 1 - \alpha$, where

$$E_2(\pi/4) \approx 1 - \Phi\!\left(\Phi^{-1}(\alpha) + \frac{p N i_0\, \epsilon}{\sqrt 2}\sqrt{\sum_{t=1}^{T}\frac{e^{2\delta t}}{\sigma_t^2}}\right).$$

**Consequences.** With any noise, the worst-case type II error tends to $1 - \alpha$ as $p \to 0$ or $\epsilon \to 0$. With noise proportional to population size ($\sigma_t = N\sigma$) it also tends to $1 - \alpha$ as $N \to \infty$ with $i_0 = 1/N$. Thus maximum likelihood estimates scatter along a line of slope one in the $(\beta, \gamma)$ plane, the growth rate $\beta - \gamma$ is well determined, and $\hat{\mathcal{R}}_0 = \hat\beta/\hat\gamma$ is highly uncertain before the peak.

## Expansion

For two Gaussian hypotheses with known variances the likelihood ratio test reduces to a test on a single projection of the data, whose standardized mean shift is $d(\omega)$, hence the formula $1 - \Phi(\Phi^{-1}(\alpha) + d)$. Under the exponential-phase approximation the incidence depends on $\theta$ through $\beta$ (a prefactor) and $\delta$ (the exponent). A perturbation with $f(\omega) \ne 0$ changes $\delta$ and produces differences growing like $e^{\epsilon t f(\omega)}$, while a perturbation along $\beta - \gamma = \text{const}$ only changes the prefactor by $\epsilon/\sqrt 2$. This direction is not exactly the least distinguishable one (for $\beta = 0.3$, $\gamma = 0.1$, $T = 30$, $\epsilon = 0.01$ and constant $\sigma_t$, $d(\omega)$ is smallest near $\omega \approx 0.268\pi$, about $0.08$ times $d(\pi/4)$; the source reaches $\pi/4$ by a first-order heuristic), but $E_2(\pi/4)$ is a lower bound on the worst case, which is all the consequences use. The structural identifiability of $(\beta, \gamma)$ (the MLE exists and is unique even before the peak) therefore does not translate into practical identifiability: the log-likelihood is nearly flat along the slope-one direction.

## Sources

- O. Melikechi, A. L. Young, T. Tang, T. Bowman, D. Dunson, J. Johndrow, "Limits of epidemic prediction using SIR models", Journal of Mathematical Biology 85 (2022) 36, Section 2 (statistical model (2)), Section 3.1 (perturbation bound, Approximation 1), Section 3.2 (Lemma 1, hypothesis test (7), Approximation 2, equations (8)–(10), Cases 1–2), <https://doi.org/10.1007/s00285-022-01804-5>.
