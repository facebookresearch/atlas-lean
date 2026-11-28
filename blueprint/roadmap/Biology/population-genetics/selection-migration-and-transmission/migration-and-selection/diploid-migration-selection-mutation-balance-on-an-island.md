# Diploid migration–selection–mutation balance on an island

An island (for example a cave) population receives immigrants from a mainland (surface) population in which allele $b$ has fixed frequency $Q \in [0,1]$. On the island genotypes have relative fitnesses $w_{bb} = 1 + s$, $w_{Bb} = 1 + hs$, $w_{BB} = 1$ with $s \ge 0$ and dominance $h \in [0,1]$. Each generation, juveniles undergo selection, then a fraction $m \in [0,1]$ of adults is replaced by immigrants, then $B$ mutates to $b$ with probability $u \in [0,1]$, then gametes unite at random. If $q$ is the frequency of $b$,

$$q_j = \frac{(1+s)q^2 + (1+hs)q(1-q)}{(1+s)q^2 + 2(1+hs)q(1-q) + (1-q)^2}, \qquad q_a = (1-m)q_j + mQ, \qquad q' = q_a + (1 - q_a)u .$$

**Equilibria.** For $s > 0$ the equilibria $\Delta q = q' - q = 0$ are the roots in $[0,1]$ of the cubic $g(q) = Aq^3 + Bq^2 + Cq + D$ with

$$A = -s(1 - 2h),\quad B = s\big(1 - m(1-u)(1-Q) - h(3 + u - m(1-u)(1-2Q))\big),$$

$$C = -(m(1-u) + u) + sh\big(1 + u - m(1-u)(1-2Q)\big),\quad D = Qm(1-u) + u .$$

Indeed $\Delta q$ times the (positive) mean fitness equals $g(q)$, so $g$ and $\Delta q$ have the same sign on $[0,1]$.

**Protected polymorphism.** $\Delta q = Qm(1-u) + u > 0$ at $q = 0$ unless $Qm = u = 0$, and $\Delta q = -m(1-Q)(1-u) < 0$ at $q = 1$ unless $m = 0$, $Q = 1$ or $u = 1$. Outside these edge cases $g(0) > 0 > g(1)$, so $g$ has one or three roots in $(0,1)$ counted with multiplicity: if they are simple, there is either one stable interior equilibrium or three in a stable–unstable–stable arrangement; at a double root (a tangency of $g$ with the axis) there are two distinct equilibria, one of them semistable. In the edge case $Qm = u = 0$ with $m > 0$, $q = 0$ is itself an equilibrium; for example $s = 1$, $h = 1/2$, $m = 1/10$, $Q = u = 0$ gives $g(q) = -\tfrac{11}{20}q^2 + \tfrac{7}{20}q$, with the two equilibria $0$ (unstable) and $7/11$ (stable).

*Correction to the source.* The source asserts the one-or-three count for every parameter value, and states Proposition 3 under the hypothesis "$m > 0$ or $u > 0$"; the example above ($m > 0$, $h \ge 1/3$) has two roots in $[0,1]$, so both statements fail when $Qm = u = 0$, and the count also fails at double roots. The statements here add the needed hypotheses: $Qm > 0$ or $u > 0$ (so $g(0) > 0$), and simple roots for the stability pattern.

**Proposition 1 (lower bound).** If $m > 0$ or $u > 0$, every equilibrium satisfies $\hat q \ge \tilde q = \dfrac{mQ(1-u) + u}{m(1-u) + u} \ge Q$, and $\tilde q$ is the equilibrium when $s = 0$.

**Proposition 2 (upper bound).** Every equilibrium satisfies $\hat q \le 1 - m(1-u)(1-Q)$, approached as $s \to \infty$ with $h = 0$.

**Proposition 3 (uniqueness).** Let $s > 0$, and let $Qm > 0$ or $u > 0$ (equivalently $D > 0$). If $h \ge 1/3$, or $h < 1/3$ and $sh > \dfrac{m(1-u) + u}{1 + u - m(1-u)(1-2Q)}$, then $g$ has exactly one root in $[0,1]$.

## Depends on

- [Migration–selection balance on an island](migration-selection-balance-on-an-island.md)
- [Hardy–Weinberg proportions](../../hardy-weinberg-law/offspring-apply.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Selection and one-way mutation only raise $q$, so $\Delta q > 0$ on $[0, \tilde q)$ (Proposition 1); immigration caps $q$ at the frequency obtained when all residents are $b$ (Proposition 2). For uniqueness, $g(1) \le 0 < g(0)$ gives a root in $(0,1]$, and the strict sign at $0$ is what the end-behaviour argument needs; for $1/2 < h \le 1$ the cubic's end behaviour forces one root below $0$ and one above $1$, for $h = 1/2$ it is quadratic, for $1/3 \le h < 1/2$ it is concave on $[0,1]$, and under the stated bound for $h < 1/3$ its derivative pattern leaves one root. A founder population starting at $q_0 = Q \le \tilde q$ climbs to the lowest equilibrium, so a "blind" island population (frequency above a threshold $q^*$) requires selection strong relative to migration: with $Q = 0.01$, $h = 0$, $s$ must be about $25m$ for $b$ to become the majority allele, but only about $3m$ when $h > 1/3$; recessive alleles need far stronger selection to reach high frequency, while dominant alleles struggle to reach fixation.

## Sources

- R. A. Cartwright, R. S. Schwartz, A. L. Merry, M. M. Howell, "The importance of selection in the evolution of blindness in cavefish", BMC Evolutionary Biology 17 (2017) 45, Eqs. 1–4, "Protected polymorphism", "Validity of equilibria", and Appendix Propositions 1–3 (the one-or-three count and the hypothesis of Proposition 3 are corrected here as explained above), <https://doi.org/10.1186/s12862-017-0876-4>, PMCID PMC5297207.
