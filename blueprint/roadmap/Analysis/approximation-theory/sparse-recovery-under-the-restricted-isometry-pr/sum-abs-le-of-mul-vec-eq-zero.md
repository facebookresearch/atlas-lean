# The null-space property under restricted isometry

Let $\iota$ be a finite index set, $s \ge 1$, and $\Phi \in \mathbb{R}^{m \times \iota}$ with the
[restricted isometry property](has-rip.md) of order $2s$ with a constant $\delta < 1$. Then for every
$h$ with $\Phi h = 0$ and every set $T_0$ of at most $s$ indices,

$$\|h_{T_0}\|_1 \le \rho\, \|h_{T_0^c}\|_1, \qquad \rho = \frac{\sqrt{2}\,\delta}{1 - \delta} .$$

Candès states the lemma for $|T_0| = s$; the proof covers $|T_0| \le s$ unchanged.

## Sources

- E. J. Candès, *The restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Lemma 2.2, eq. (15)
