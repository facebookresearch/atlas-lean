# Formula for the positive predictive value

For all real $\pi$, $\mathrm{se}$ and $\mathrm{sp}$, the [positive predictive value](ppv.md) is

$$
\mathrm{PPV}(\pi, \mathrm{se}, \mathrm{sp}) =
\frac{\pi\, \mathrm{se}}{\pi\, \mathrm{se} + (1 - \pi)(1 - \mathrm{sp})},
$$

with the convention $x / 0 = 0$, so it is $0$ when the denominator vanishes.
