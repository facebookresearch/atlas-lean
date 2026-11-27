# Delayed mutual information of phase signals under a von Mises ansatz

**Setting.** Let $\varphi_i(t), \varphi_j(t)$ be the phases (in $\mathbb{R}/2\pi\mathbb{Z}$) of two units of a stationary stochastic oscillator network. For a lag $d \in \mathbb{R}$ the **delayed mutual information** is

$$\mathrm{dMI}_{i,j}(d) = \int\!\!\int p^{(d)}_{i,j}(x, y) \, \ln \frac{p^{(d)}_{i,j}(x,y)}{p_i(x)\, p_j(y)} \, dx \, dy ,$$

where $p_i$ is the law of $\varphi_i(t)$ and $p^{(d)}_{i,j}$ the joint law of $(\varphi_i(t), \varphi_j(t+d))$. Asymmetry of $d \mapsto \mathrm{dMI}_{i,j}(d)$ about $d = 0$ indicates the dominant direction of information sharing; the signed difference of the areas under the curve for $d > 0$ and $d < 0$ is used as the directed strength $\delta \mathrm{MI}_{i,j}$ (positive: predominantly from $i$ to $j$), and the collection $\{\delta\mathrm{MI}_{i,j}\}$ is an *information routing pattern*.

**Statement.** Assume (i) stationarity with a freely drifting common phase, so that each marginal is uniform, $p_i = p_j = 1/(2\pi)$; and (ii) the von Mises ansatz for the conditional law of the lagged phase,

$$p^{(d)}_{i,j}(x, y) = \frac{1}{2\pi} \cdot \frac{\exp\big(\kappa \cos(y - x - \mu)\big)}{2\pi I_0(\kappa)}, \qquad \kappa = \kappa_{i,j}(d) \ge 0 ,$$

with $I_n$ the modified Bessel function of the first kind of order $n$ and $\mu$ the locked phase offset. Then

$$\mathrm{dMI}_{i,j}(d) = \kappa \, \frac{I_1(\kappa)}{I_0(\kappa)} - \ln I_0(\kappa), \qquad \kappa = \kappa_{i,j}(d).$$

This function of $\kappa$ is $0$ at $\kappa = 0$, strictly increasing on $[0, \infty)$, behaves like $\kappa^2/4$ as $\kappa \to 0$ and like $\tfrac12 \ln(2\pi\kappa/e)$ as $\kappa \to \infty$. Hence all dependence of the information sharing on unit dynamics, coupling functions, topology, noise and the collective reference state enters only through the concentration (inverse variance) $\kappa_{i,j}(d)$ of the lagged phase difference.

## Expansion

With uniform marginals, $\mathrm{dMI} = H(\varphi_j(t+d)) - H(\varphi_j(t+d) \mid \varphi_i(t)) = \ln 2\pi - \big[\ln(2\pi I_0(\kappa)) - \kappa\, \mathbb{E}\cos(y - x - \mu)\big]$, and $\mathbb{E}\cos(y - x - \mu) = I_1(\kappa)/I_0(\kappa)$ for a von Mises law, giving the formula. Writing $A(\kappa) = I_1/I_0$ and using $I_0' = I_1$, the derivative is $\kappa A'(\kappa) > 0$. The large-$\kappa$ limit coincides with the mutual information of a Gaussian phase difference of variance $1/\kappa$, as expected when the phase-locked fluctuations are small. In the source the concentrations $\kappa_{i,j}(d)$ are computed from the small-noise linearization of the phase dynamics around a phase-locked state (coupled Ornstein–Uhlenbeck processes), and the predicted curves match simulations of Goodwin-type gene oscillators, Wilson–Cowan neural masses and Stuart–Landau oscillators; an analogous closed form is derived for the delayed transfer entropy.

## Sources

- C. Kirst, M. Timme, D. Battaglia, "Dynamic information routing in complex networks", Nature Communications 7 (2016), 11061, Results ("Information routing via collective dynamics", "Information exchange in phase signals", Eq. (4) and Supplementary Note 4, Theorems 1–2) and Methods ("Analytic derivation of the dMI and dTE curves"), <https://doi.org/10.1038/ncomms11061> (PMC4832059).
