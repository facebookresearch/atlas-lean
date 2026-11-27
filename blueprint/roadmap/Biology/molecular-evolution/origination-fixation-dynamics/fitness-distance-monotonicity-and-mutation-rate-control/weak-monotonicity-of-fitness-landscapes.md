# Weak monotonicity of fitness landscapes

Let $(\Omega, d)$ be a metric space with a Borel probability measure $P$, $f : \Omega \to \mathbb R$ a $P$-measurable fitness function, and $\top$ a local optimum: $f(\top) = \sup\{f(\omega) : \omega \in E\}$ for some neighbourhood $E$. For a point $a$, let $\mathbb E[f(a)]$ be the mean fitness over the sphere of points at distance $d(\top, a)$ from $\top$ and $\mathbb E[d(\top, a)]$ the mean distance to $\top$ over the level set $\{f = f(a)\}$ (conditional expectations under $P$).

- $f$ is **weakly monotonic relative to $d$ at $\top$** if, for points $a, b$ taken from any sequence with $d(\top, \omega_n) \to 0$,

$$\lim_{d(\top, b) \to 0} P\bigl\{ -d(\top, a) \le -d(\top, b) \implies \mathbb E[f(a)] \le \mathbb E[f(b)] \bigr\} = 1 .$$

- $d$ is **weakly monotonic relative to $f$ at $\top$** if, along sequences with $f(\omega_n) \to f(\top)$,

$$\lim_{f(b) \to f(\top)} P\bigl\{ f(a) \le f(b) \implies -\mathbb E[d(\top, a)] \le -\mathbb E[d(\top, b)] \bigr\} = 1 .$$

- $f$ and $d$ are **weakly isomorphic** at $\top$ if both hold.

**Theorem.**

1. If $f$ is continuous at $\top$, then $f$ is weakly monotonic relative to $d$ at $\top$.
2. If $f$ maps open balls $B[\top, \delta) \subseteq E$ onto intervals $(f(\top) - \varepsilon, f(\top)]$ (the landscape is open at $\top$), then $d$ is weakly monotonic relative to $f$ at $\top$.
3. If both conditions hold, $f$ and $d$ are weakly isomorphic at $\top$.

Local monotonicity implies average local monotonicity, which implies weak monotonicity; the converses fail, and continuous landscapes may be nowhere monotonic in the strict sense while remaining weakly monotonic at every optimum.

## Expansion

Continuity at $\top$ gives, for any increasing sequence of fitness levels $f(\top) - \varepsilon_n \uparrow f(\top)$, a decreasing sequence of radii $\delta_n \downarrow 0$ with $f > f(\top) - \varepsilon_n$ on $B[\top, \delta_n)$. Comparing a point $a$ farther out with a point $b$ inside a smaller ball, the event that the closer point has higher mean fitness has probability tending to $1$ as the balls shrink; openness gives the symmetric statement with the roles of fitness and distance exchanged. The theorem extends to quasi-pseudometrics, hence to essentially any topology used on sequence or structure spaces. Biologically, in any landscape continuous and open at an optimum, fitness becomes an increasingly reliable proxy for distance near the optimum, so fitness-based control of the mutation rate should mimic distance-based control, with the rate increasing as fitness decreases; this was observed in complete transcription-factor binding landscapes.

## Sources

- R. V. Belavkin, A. Channon, E. Aston, J. Aston, R. Krašovec, C. G. Knight, "Monotonicity of fitness landscapes and mutation rate control", *Journal of Mathematical Biology* (2016), section "Monotonicity of fitness and distance" (definitions of local, average and weak monotonicity, Theorem 1, Hypothesis 1) and Appendix 3, <https://doi.org/10.1007/s00285-016-0995-3> (PMC5061859).
