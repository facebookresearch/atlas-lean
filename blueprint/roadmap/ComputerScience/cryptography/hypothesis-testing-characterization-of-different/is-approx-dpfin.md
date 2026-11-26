# Approximate differential privacy with finite outputs

Let $M$ assign to each database a probability mass function on a finite type $\Omega$, let $\mathrm{adj}$ be a relation on databases and $\varepsilon, \delta \in \mathbb{R}$. The mechanism is $(\varepsilon, \delta)$-differentially private in finite-sum form when $\varepsilon \ge 0$, $\delta \ge 0$, and for every ordered pair with $\mathrm{adj}(d, d')$ and every $S \subseteq \Omega$,

$$
\sum_{w \in S} M(d)(w) \le e^{\varepsilon} \sum_{w \in S} M(d')(w) + \delta,
$$

as an inequality of real numbers.
