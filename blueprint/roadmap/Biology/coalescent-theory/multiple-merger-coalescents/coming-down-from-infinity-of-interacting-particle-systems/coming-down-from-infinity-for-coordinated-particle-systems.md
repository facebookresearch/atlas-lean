# Coming down from infinity for coordinated particle systems

**Model.** Let $V$ be a finite set of sites. A coordinated particle system is a Markov process $X(t) \in (\mathbb{N}_0 \cup \{\infty\})^V$ driven by finite measures on $[0,1]$: a coalescence measure $\Lambda_v$, a death measure $D_v$, migration measures $M_{vu}$ and reproduction measures $R_{vu}$. From a finite state $\pi$, for $1 \le k \le \pi(v)$ (and $k \ge 2$ for coalescence), with $\beta_k(z) = \binom{\pi(v)}{k} z^k (1-z)^{\pi(v)-k}$:
- $k$ particles migrate from $v$ to $u$ at rate $\int_0^1 \beta_k(z)\, M_{vu}(dz)/z$;
- $k$ particles die at $v$ at rate $\int_0^1 \beta_k(z)\, D_v(dz)/z$;
- $k$ particles at $v$ each produce one offspring at $u$ at rate $\int_0^1 \beta_k(z)\, R_{vu}(dz)/z$;
- $k$ particles at $v$ merge into one at rate $\int_0^1 \beta_k(z)\, \Lambda_v(dz)/z^2$.

All particles at a site act through one common fraction $z$, so large events are coordinated. A monotone Poisson construction extends the process to infinite initial states, and $X$ *comes down from infinity* if $\sum_v X_v(t) < \infty$ for all $t > 0$ almost surely.

**Standing assumption.** None of the measures $\Lambda_v$, $D_v$, $M_{vu}$, $R_{vu}$ has an atom at $1$. This is assumed throughout the paragraph on $\Lambda$-strong measures and the theorem below (an atom at $1$ lets all particles at a site act at once after an exponential time, so the system could come down from infinity, but not instantaneously).

**$\Lambda$-strong measures.** For a $\Lambda$ whose $\Lambda$-coalescent comes down from infinity, a migration (or reproduction) measure $M$ is *$\Lambda$-strong* if, in the two-site system with coalescence $\Lambda$ at $u$, migration $M$ from $u$ to $v$, $X_u(0) = \infty$, $X_v(0) = 0$ and all other measures zero, infinitely many particles reach $v$ before every time $t > 0$ almost surely. If $M(\{0\}) > 0$ or $\mathbb{E}[-\log Y] = \infty$ for $Y \sim M/M([0,1])$, then $M$ is $\Lambda$-strong for every $\Lambda$; adding a death measure without an atom at $1$ does not change $\Lambda$-strength.

**Theorem.**
1. *(Sufficient condition to stay infinite.)* A system started with infinitely many particles at $v_1$ does not come down from infinity if there is a path $v_1, v_2, \dots, v_k$ of sites such that the $\Lambda_{v_k}$-coalescent does not come down from infinity and, for each $i < k$, $M_{v_i v_{i+1}}$ or $R_{v_i v_{i+1}}$ is $\Lambda_{v_i}$-strong.
2. *(Converse without reproduction.)* If there is no reproduction and $X$ stays infinite, then some site $v_1$ starts with infinitely many particles and such a path from $v_1$ exists.
3. Without death or reproduction, if every $\Lambda_v$-coalescent comes down from infinity, then $X$ comes down from infinity from any initial state.
4. *(Beta-type coalescence.)* Let $\Lambda_u(dz) = f(z)\,dz$ with $f(z) \sim B z^{1-\alpha}$ as $z \to 0$, $\alpha \in (1,2)$, with death at $u$ and migration $M_{uv}$ from $u$ to $v$ only. Let $W = UY$ with $U \sim \mathrm{Unif}[0,1]$ independent of $Y \sim M_{uv}/M_{uv}([0,1])$. If $\sum_{n \ge 1} \mathbb{E}[(1-W)^n]\, n^{1-\alpha} = \infty$, then infinitely many particles jump from $u$ to $v$ before every $t > 0$ almost surely; if the series converges, only finitely many do.

## Depends on

- [Schweinsberg's criterion for coming down from infinity](../speed-of-coming-down-from-infinity/schweinsberg-criterion-lambda-coalescent-comes-d.md)

## Expansion

An infinite population can survive only by escaping a site that would compress it: particles must be shipped out faster than the coalescence at their site removes them, and must end at a site whose own coalescent cannot compress infinitely many particles. Strength of a migration measure compares the number $\approx n$ of particles present at the beginning of the descent, which under Beta$(2-\alpha,\alpha)$-type coalescence falls like $t^{-1/(\alpha-1)}$, with the chance that a migration event of fraction $Y$ takes away at least one particle; the series in part 4 is the resulting Borel–Cantelli sum. The seed-bank coalescent with simultaneous switching is the special case with Kingman coalescence at the active site and migration measures in both directions.

## Sources

- Varun Sreedhar, "Coming down from infinity for coordinated particle systems", Stoch. Process. Appl. 197 (2026), 104936, <https://doi.org/10.1016/j.spa.2026.104936>. Numbering follows the arXiv version, arXiv:2506.15736 (2025): Section 1.1 rates, Definition of $\Lambda$-strong, Theorems 1–4, Propositions 1–4, <https://doi.org/10.48550/arXiv.2506.15736>.
