# Strong NP-hardness of the copy-number profile transformation problem

**Model.** A copy-number profile (CNP) is a vector $u=(u_1,\dots,u_n)\in\mathbb N^n$. An event is $e=(s,t,\delta)$ with $1\le s\le t\le n$ and $\delta\in\mathbb Z\setminus\{0\}$ (amplification if $\delta>0$, deletion if $\delta<0$); applying it gives $u\langle e\rangle$ with

$$u'_i=\begin{cases}\max(u_i+\delta,0) & i\in[s,t]\text{ and }u_i>0,\\ u_i&\text{otherwise,}\end{cases}$$

so a lost position can never be regained. A cost function $f:\mathbb N\times\mathbb Z\to\mathbb N_{>0}\cup\{\infty\}$ prices an event by $\operatorname{cost}_f(u,e)=\max_{i\in[s,t]}f(u_i,\delta)$, a sequence by the sum of its event costs, and $d_f(u,v)$ is the minimum cost of a sequence transforming $u$ into $v$. $f$ is *unit-cost* if $f\in\{1,\infty\}$ (examples: $\mathrm{mdc}$, allowing only $\delta=\pm1$; $\mathrm{dbl}$, allowing $u_i+\delta\le 2u_i$; $\mathrm{any}$, allowing everything), and *deletion-permissive* if $f(c,\delta)=1$ for all $\delta<0$.

**CNP-transformation problem.** Given CNPs $u,v$, a cost function $f$ and $k$, decide whether $d_f(u,v)\le k$.

**Theorem.** For every deletion-permissive unit-cost function $f$, the CNP-transformation problem is strongly NP-hard, even when $u$ and $v$ have no null (zero) positions, and even if only deletions are used.

**Supporting facts.** For CNPs $u,v$ with no null positions and $w=u-v$:

- (Monotonicity) $d_f(u,v)\ge d_f(u-\{i\},v-\{i\})$ for every position $i$ and every $f$.
- (Amp-first reordering) if $u\langle E\rangle=v$, then every reordering of $E$ that puts all amplifications before all deletions also transforms $u$ into $v$.
- (Staircase bound) if $w$ has a staircase $[a,b]$, i.e. $0<w_a<w_{a+1}<\dots<w_b$, of length $k=b-a+1$, then $d_f(u,v)\ge k$ for every unit-cost $f$.

## Expansion

Each step of a staircase needs its own event boundary, which gives the lower bound. When a staircase on $[1,k]$ is matched exactly by $d_f(u,v)=k$, an optimal solution can be taken to be *smooth*: event $i$ is $(i,b_i,w_{i-1}-w_i)$ with $b_i\ge k$, peeling off one step at a time (the technical core of the proof). The hardness proof reduces from 3-PARTITION (strongly NP-hard) using instances whose difference vector contains such a staircase, so that by the smoothness property only staircase-peeling solutions can meet the bound $k$; the full reduction is given in the supplementary material of the source. Strong hardness means the problem stays hard even when copy numbers are polynomially bounded.

## Sources

- G. Cordonnier, M. Lafond, "Comparing copy-number profiles under multi-copy amplifications and deletions", *BMC Genomics* 21(Suppl 2):198 (2020), Propositions 1 and 2, Lemmas 1 and 2, Theorem 1, <https://doi.org/10.1186/s12864-020-6611-3>, PMCID: PMC7160889.
