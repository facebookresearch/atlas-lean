# Amplitude and peak timing from harmonic seasonal regression

Let $y(t)$ be a weekly incidence series (for instance, influenza-positive specimens standardized by the number tested), $t$ the week index, and $\omega = 2\pi/52.18$ the annual angular frequency in radians per week. Fit by least squares

$$y(t) \;=\; a + b\cos(\omega t) + c\sin(\omega t) + d\cos(2\omega t) + e\sin(2\omega t) + \varepsilon(t).$$

Then the seasonal component equals

$$A_1\cos(\omega t - \varphi_1) + A_2\cos(2\omega t - \varphi_2), \qquad A_1 = \sqrt{b^2 + c^2},\quad A_2 = \sqrt{d^2 + e^2},$$

with $\varphi_1 = \operatorname{atan2}(c, b)$ and $\varphi_2 = \operatorname{atan2}(e, d)$. Hence:

1. $A_1$ and $A_2$ are the amplitudes of the annual and semi-annual periodicities, and $A_1/\bar y$, $A_2/\bar y$ their relative amplitudes, comparable across series of different mean $\bar y$.
2. The annual harmonic peaks at weeks $t \equiv \varphi_1/\omega \pmod{2\pi/\omega}$.
3. The ratio $A_2/(A_1 + A_2) \in [0,1]$ is near $0$ for a purely annual pattern and near $1$ for a dominant semi-annual pattern (two peaks a year).

## Expansion

The identity $b\cos\theta + c\sin\theta = \sqrt{b^2 + c^2}\cos(\theta - \operatorname{atan2}(c,b))$ follows from the cosine angle-difference formula, with $\cos\varphi = b/A$ and $\sin\varphi = c/A$, and it is maximized at $\theta = \varphi$. The regressors are fixed functions of $t$, so ordinary least squares applies; because weekly incidence is autocorrelated, confidence intervals for amplitudes, peak timing and the ratio are obtained by block bootstrap rather than from the residual variance. Applied to laboratory-confirmed influenza across 30 Chinese provinces (2005–2011), the relative annual amplitude of influenza A was about $140\%$ in the north versus $37\%$ in the south, epidemics peaked in January–February north of $33^\circ$N and in April–June south of $27^\circ$N, and provinces at intermediate latitudes had periodicity ratios above $0.6$ (semi-annual peaks). This supported vaccination campaigns timed about 4–6 months apart in northern and southern China.

## Sources

- H. Yu, W. J. Alonso, L. Feng, Y. Tan, Y. Shu, W. Yang, C. Viboud, "Characterization of regional influenza seasonality patterns in China and implications for vaccination strategies: spatio-temporal modeling of surveillance data", *PLoS Medicine* 10(11) (2013) e1001552, Abstract and Methods (seasonal regression models with annual and semi-annual harmonic terms), <https://doi.org/10.1371/journal.pmed.1001552> (PMC3864611).
