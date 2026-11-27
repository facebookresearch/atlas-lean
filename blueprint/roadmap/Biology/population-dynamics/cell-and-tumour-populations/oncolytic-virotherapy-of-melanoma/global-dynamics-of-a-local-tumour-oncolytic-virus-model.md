# Global dynamics of a local tumour–oncolytic virus model

**Model.** At the primary tumour site, normalised densities of uninfected tumour cells $x$ and virus-infected tumour cells $y$ satisfy

$$\dot x = x(1-x-y) - \frac{\theta xy}{\alpha+y}, \qquad \dot y = r y(1-x-y) + \frac{\theta xy}{\alpha+y} - \gamma y,$$

with logistic growth sharing a common carrying capacity, saturating infection with maximal rate $\theta>0$ and half-saturation $\alpha>0$, growth rate $r>0$ of infected cells and virus-induced death rate $\gamma>0$ of infected cells.

**Theorem.** The system has no closed orbits in $\mathbb{R}^2_+$, and:

1. If $\gamma>\max\{r, \theta/\alpha\}$, the only nonnegative equilibria are $(0,0)$ (a saddle) and the tumour-only state $(1,0)$, which is globally asymptotically stable.
2. If $r<\gamma<\theta/\alpha$, a positive coexistence equilibrium $(x_*,y_*)$ exists and is globally asymptotically stable, while $(0,0)$ and $(1,0)$ are saddles.
3. If $r>\gamma$: $(1,0)$ is globally asymptotically stable when $\theta<\alpha\gamma$; $(x_*,y_*)$ is globally asymptotically stable when $\alpha\gamma<\theta<\gamma\big(\frac{\alpha}{r-\gamma}+\frac1r\big)$; and the infected-only state $\big(0, \frac{r-\gamma}{r}\big)$, with uninfected tumour cells eliminated, is globally asymptotically stable when $\theta>\gamma\big(\frac{\alpha}{r-\gamma}+\frac1r\big)$.

## Expansion

With the Dulac function $1/(xy)$ the divergence of the scaled field is negative in the open quadrant, so there are no periodic orbits and, by Poincaré–Bendixson, bounded trajectories converge to equilibria. The stability of $(1,0)$ against infection is decided by the invasion rate $\theta/\alpha-\gamma$ of infected cells into a full tumour, and that of $(0,(r-\gamma)/r)$ against uninfected cells by the sign of $1-y-\theta y/(\alpha+y)$ at $y=(r-\gamma)/r$, which gives the threshold $\gamma\big(\frac{\alpha}{r-\gamma}+\frac1r\big)$. The equilibrium that is locally stable is then globally attracting.

## Sources

- T. Ramaj, X. Zou, "On the treatment of melanoma: a mathematical model of oncolytic virotherapy", *Mathematical Biosciences* 365 (2023), 109073, Section 3, Proposition 3.1 and Theorems 3.2–3.3, <https://doi.org/10.1016/j.mbs.2023.109073> (preprint arXiv:2309.00821).
