# Closed form of the zero-agnostic copy number distance

**Events.** A copy number profile is a vector $p \in \mathbb{Z}^n$ of copy numbers at $n$ ordered loci. A **zero-agnostic copy number event** $c_{s,t,b}$ with $1 \le s \le t \le n$ and $b \in \{+1, -1\}$ maps $p$ to $c_{s,t,b}(p)_i = p_i + b$ for $s \le i \le t$ and $p_i$ otherwise, regardless of whether loci have zero copies (Definition 3). The **ZCNT distance** $d(p, p')$ is the minimum number of such events transforming $p$ into $p'$.

**Delta profiles.** A delta profile is $q \in \mathbb{Z}^{n+1}$ with $\sum_i q_i = 0$; write $D_{n+1}$ for the set of them. The **delta map** $\Delta : \mathbb{Z}^n \to D_{n+1}$ (Definition 5) is

$$\Delta(p)_1 = p_1 - 2, \qquad \Delta(p)_i = p_i - p_{i-1}\ (2 \le i \le n), \qquad \Delta(p)_{n+1} = 2 - p_n,$$

the adjacent differences after padding $p$ with diploid loci on both sides. A **delta event** $\delta_{s,t,b}$ adds $b$ to entry $s$ and subtracts $b$ from entry $t + 1$ (Definition 6).

**Results.**

- (Proposition 1) $\Delta$ is a bijection $\mathbb{Z}^n \to D_{n+1}$.
- (Theorem 1) $p' = c_{s,t,b}(p)$ iff $\Delta(p') = \delta_{s,t,b}(\Delta(p))$; hence compositions of events correspond (Corollary 1) and events commute.
- (Theorem 2, Corollary 2) For all $p, p' \in \mathbb{Z}^n$,

$$d(p, p') = \tfrac12 \big\|\Delta(p) - \Delta(p')\big\|_1 ,$$

so $d$ is a metric computable in $O(n)$ time.
- (Corollary 3) For two profiles $p, p'$, $\min_{r \in \mathbb{Z}^n} \{d(r, p) + d(r, p')\} = d(p, p')$, attained at $r = p$ and $r = p'$.

## Expansion

A segmental gain or loss on $[s, t]$ changes only the jumps at its two ends, so in delta coordinates an event moves one unit of mass from position $t+1$ to position $s$ (or back). Each delta event lowers $\|q\|_1$ by at most $2$, which gives $d'(q, 0) \ge \tfrac12 \|q\|_1$; conversely, the balancing condition $\sum_i q_i = 0$ guarantees a positive and a negative entry whenever $q \ne 0$, and one event cancels a unit of each, so $\tfrac12 \|q\|_1$ events suffice. Translation invariance $d'(q, q') = d'(q - q', 0)$ yields the general formula. The zero-agnostic relaxation is what makes this work: in the classical model, once a locus reaches zero copies it cannot be amplified, which destroys the independence of the delta coordinates and makes the distance much harder to compute.

## Sources

- H. Schmidt, P. Sashittal, B. J. Raphael, "A zero-agnostic model for copy number evolution in cancer", PLoS Computational Biology 19 (2023) e1011590, Definitions 3–6, Proposition 1, Theorems 1–2, Corollaries 1–3, <https://doi.org/10.1371/journal.pcbi.1011590> (PMC10662746).
