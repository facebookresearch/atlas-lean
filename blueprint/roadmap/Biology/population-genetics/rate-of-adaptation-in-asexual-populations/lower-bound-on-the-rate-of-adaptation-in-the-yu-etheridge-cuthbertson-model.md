# Lower bound on the rate of adaptation in the Yu–Etheridge–Cuthbertson model

**Setting.** A population of fixed size $N$ is described by integer fitnesses $X_t = (X_t^1,\dots,X_t^N)$. Each individual acquires mutations at rate $\mu > 0$, beneficial with probability $q \in (0,1]$ (fitness $+1$) and deleterious otherwise (fitness $-1$); selective advantage per beneficial mutation is $\gamma > 0$. For all $i,j$ the transitions are

$$X^i \to X^i + 1 \ \text{at rate } q\mu, \qquad X^i \to X^i - 1 \ \text{at rate } (1-q)\mu, \qquad X^i \to X^j \ \text{at rate } \frac1N + \frac{\gamma}{N}\,(X^j - X^i)\vee 0,$$

the last term combining Moran resampling with selection (fitter individuals replace less fit ones). The centred process $X^i - \overline{X}$ is ergodic, and in stationarity the mean fitness grows linearly, $\mathbb{E}^\pi[\overline{X}_t] = \big(\mu(2q-1) + \gamma\,\mathbb{E}^\pi[c_2]\big)t$, where $c_2$ is the fitness variance; the long-run rate of adaptation is known to be at most $C\log N/(\log\log N)^2$.

**Theorem.** Fix $t > 0$, let

$$\mathcal{T} = \frac{16(\log\log N)^2}{\gamma\log N},$$

let $M$ be the integer with $M < t/(2\mathcal{T}) \le M+1$, and let $X_s^+ = \max_i X_s^i$. Then

$$\lim_{N\to\infty}\mathbb{P}\Big(X_s^+ \ge \tfrac{M s}{2}\ \text{for all } s \in [\mathcal{T},t]\Big) = 1 .$$

Hence, with probability tending to one, the fittest individual gains at least one fitness unit per time $2\mathcal{T}$, so the maximal fitness advances at rate of order $\gamma\log N/(\log\log N)^2$, matching the heuristic prediction and the upper bound up to constants.

## Expansion

The proof shows that in each time window of length $\mathcal{T}$ the current fittest class produces a new, strictly fitter class that survives. Over such a window an individual is hit by a potentially fitness-lowering event at rate $d = (1+q)\mu + 1$, independent of $N$; with width $\mathcal{W} = \log N/(8\log\log N)$ and $w = \gamma\mathcal{W}/2$, the descendant count $Z_{\mathcal{T}}$ of an individual leading by about $\mathcal{W}$ is compared with a branching process, giving $w\,\mathbb{P}(Z_{\mathcal{T}} = 0) \to d$ and $(\log N)\,\mathbb{P}(Z_{\mathcal{T}} = 1) \to 1$. Since selection gives the leading class a growth rate proportional to $\gamma$ times its fitness lead, within $\mathcal{T}$ the class grows past a width $\mathcal{W}$, and among at least $\mathcal{W}$ (or $N/2$) independent individuals, at least two acquire a further beneficial mutation that survives. Iterating over the $M$ windows in $[0,t]$ gives the linear lower envelope. The $(\log\log N)^2$ correction reflects the time the leading class needs to grow from one individual to a size where its next beneficial mutation is likely, the same balance that gives the travelling-wave heuristic of Desai–Fisher and Rouzine–Brunet–Wilke.

## Sources

- Michael Kelly, "Lower Bound on the Rate of Adaptation in an Asexual Population", arXiv:1508.04469 (2015), Section 1 (model, previous results, Theorem 1), Section 2 (Propositions 2–4 and 7, Lemmas 5–6), <https://doi.org/10.48550/arXiv.1508.04469>.
