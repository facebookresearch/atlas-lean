# Time average of 1/r² over an elliptic orbit is 1/(a²√(1 − e²))

Let $a > 0$, $0 \le e < 1$ and $h > 0$, and let $r(\theta) = a(1 - e^2)/(1 + e\cos\theta)$ for every
real $\theta$: the distance from a focus on an ellipse with semi-major axis $a$ and eccentricity
$e$. Assume, as a hypothesis, the area identity

$$\int_0^{2\pi} r(\theta)^2\,d\theta = 2\pi a^2\sqrt{1 - e^2},$$

twice the area $\pi a^2\sqrt{1 - e^2}$ of the ellipse. Weighting the angle by the areal law
$dt = r^2\,d\theta/h$ (with $h$ the constant of the areal law, twice the areal velocity), the time
average of $1/r^2$ over one revolution is

$$\frac{\int_0^{2\pi} \frac{1}{r(\theta)^2}\,\frac{r(\theta)^2}{h}\,d\theta}
{\int_0^{2\pi} \frac{r(\theta)^2}{h}\,d\theta} = \frac{1}{a^2\sqrt{1 - e^2}}.$$
