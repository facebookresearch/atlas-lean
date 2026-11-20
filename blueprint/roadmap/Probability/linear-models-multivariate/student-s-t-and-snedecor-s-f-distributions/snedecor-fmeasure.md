# Snedecor's F distribution

Snedecor's F distribution with $(d_1, d_2)$ degrees of freedom (Casella and Berger, Definition 5.3.6)
has the density
$$\frac{\Gamma\big(\frac{d_1 + d_2}{2}\big)}{\Gamma\big(\frac{d_1}{2}\big)\,\Gamma\big(\frac{d_2}{2}\big)} \left(\frac{d_1}{d_2}\right)^{d_1/2} x^{d_1/2 - 1} \left(1 + \frac{d_1 x}{d_2}\right)^{-(d_1 + d_2)/2}$$
for $x > 0$, and $0$ elsewhere. For $d_1, d_2 \ge 1$ it is a probability distribution, and it is the
law of $(V_1/d_1)/(V_2/d_2)$ for independent $V_1 \sim \chi^2_{d_1}$ and $V_2 \sim \chi^2_{d_2}$; for
$d_1 = 0$ or $d_2 = 0$ the measure is defined to be zero.
