# Arithmetic fitness model of periodical species and prime or multiple periods

**Model.** Two species $\mathcal{C}_1, \mathcal{C}_2$ emerge synchronously every $c_1$ and $c_2$ years, respectively ($c_1, c_2 \ge 2$ integers). Over the window $[1, T]$, $T = c_1 c_2$, species $\mathcal{C}_1$ emerges $c_2$ times and $\mathcal{C}_2$ emerges $c_1$ times. Local fitness values $f_i \in \{-1, 0, 1\}$ (bad, neutral, good) are assigned only to emergent years and are summarized by the **fitness tuple**

$$
v = (\nu_1, \nu_2, \nu_3, \nu_4) = \big(f_1(1,0),\ f_2(0,1),\ f_1(1,1),\ f_2(1,1)\big) \in \{-1, 0, 1\}^4,
$$

where $\nu_1, \nu_2$ are the payoffs of emerging alone and $\nu_3, \nu_4$ the payoffs of co-emerging. The global fitness of each species is its average payoff per emergence,

$$
F_1(c_1, c_2) = \frac{1}{c_2}\sum_{t=1}^{T} f_1(\chi_1(t), \chi_2(t)), \qquad F_2(c_1, c_2) = \frac{1}{c_1}\sum_{t=1}^{T} f_2(\chi_1(t), \chi_2(t)),
$$

with $\chi_i(t) = 1$ in emergence years. Co-emergences in $[1, T]$ occur at the multiples of $\operatorname{lcm}(c_1, c_2)$, so their number is $g = \gcd(c_1, c_2)$, and

$$
F_1 = \frac{\nu_1 (c_2 - g) + \nu_3\, g}{c_2}, \qquad F_2 = \frac{\nu_2 (c_1 - g) + \nu_4\, g}{c_1} .
$$

**Evolutionary dynamics.** Each species in turn proposes a new period $c_i + k$, $k \in \{-p, \dots, p\}$, and accepts it if its own global fitness increases. A pair $(c_1, c_2)$ is a **$p$-fixed point** if no such unilateral change increases either fitness, and a **global fixed point** if this holds for every $p$. Up to exchanging the species and removing tuples with identical fixed-point sets, the $81$ tuples reduce to $18$ cases in four classes.

**Proposition (mutual avoidance gives coprime periods).** For the tuple $v_6 = (1, 1, -1, -1)$ (each species does well alone and badly when co-emerging, as with shared predators or competition), every pair with $\gcd(c_1, c_2) = 1$ is a global fixed point, and there are infinitely many further local fixed points.

**Proposition (dependence gives multiple periods).** For $v_{16} = (-1, 0, 1, 0)$ (species $\mathcal{C}_1$ benefits only from co-emerging and $\mathcal{C}_2$ is indifferent), every pair with $c_2 \mid c_1$ is a global fixed point. Symmetrically, $v_{18}$ has the global fixed points $c_1 \mid c_2$, and $v_{15} = (0, -1, 1, 0)$ has the global fixed points $c_1 = c_2$.

**Proposition (prime periods as local attractors).** For $v_{17}$ there is no global fixed point, but every pair with $c_1$ prime and $c_2 < c_1 - 1$ is a local ($p = 1$) fixed point. For $v_9 = (-1, 1, 1, -1)$ (predator-prey: $\mathcal{C}_1$ gains from meeting $\mathcal{C}_2$, which loses), only local fixed points exist: every pair in which $c_2$ is prime and divides none of $c_1 - 1, c_1, c_1 + 1$ is one (then $\gcd(c_1 + k, c_2) = 1$ for $|k| \le 1$, so $F_1 = 2/c_2 - 1$ cannot rise, and $g = 1$ already maximizes $F_2 = 1 - 2g/c_1$), and the species $\mathcal{C}_1$ disappears.

## Expansion

With $g = \gcd(c_1, c_2)$, the tuple $v_6$ gives $F_1 = 1 - 2g/c_2$, which is maximal over $c_1$ exactly when $g = 1$; any change of $c_1$ keeps $g \ge 1$ and so cannot raise $F_1$, and symmetrically for $F_2$. For $v_{16}$, $F_1 = 2g/c_2 - 1$ is maximal when $g = c_2$, that is, when $c_2$ divides $c_1$, while $F_2 \equiv 0$ imposes nothing. Prime periods arise because a prime $c$ shares no factor with any smaller period, so a predator or competitor with a shorter cycle coincides with it only once per window, the minimum possible. Arithmetically, the four principles (coprime periods, a prime period, equal periods, one period a multiple of the other) reproduce prime life cycles such as the 13- and 17-year cicadas and the large composite cycles of bamboos, such as multiples of small primes up to 120 years.

## Sources

- Eric Goles, Ivan Slapničar and Marco A. Lardies, "Universal evolutionary model for periodical species", arXiv (2020), Section 2 (model, fitness tuples and classes, evolution algorithm, $p$-fixed points), Lemma 1, Propositions 1–4 and the appendix proofs, <https://doi.org/10.48550/arXiv.2010.00940>.
