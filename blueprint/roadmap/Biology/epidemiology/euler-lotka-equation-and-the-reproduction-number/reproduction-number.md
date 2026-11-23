# Reproductive number from growth rate and generation interval

For a measure $g$ on $\mathbb{R}$ (the law of the generation interval) and a growth rate
$r \in \mathbb{R}$, the reproductive number is

$$R = \frac{1}{M_g(-r)}, \qquad M_g(-r) = \int e^{-ra} \, g(da)$$

(Wallinga–Lipsitch 2007, eq. 2.9). The integral is taken to be $0$ when $a \mapsto e^{-ra}$ is not
$g$-integrable, and $1/0$ is read as $0$, so $R = 0$ in that case.
