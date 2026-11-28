# Gillespie–Wright–Fisher limit of two-type logistic branching with selection

**Model.** Individuals of types $+$ and $-$ reproduce independently: at rate $\mu^\pm_K(i)$ an individual of type $\pm$ is replaced by $i \ge 0$ children. The mean net reproduction rates are $\sum_i (i-1)\mu^\pm_K(i) = \mathfrak m + \mathfrak s^\pm/K + o(1/K)$ with $\mathfrak m > 0$, and the offspring second moments converge, $\sum_i (i-1)^2\mu^\pm_K(i) \to \mathfrak v^\pm > 0$. Each individual also dies at rate $\mathfrak m/K$ times the total population size (logistic competition, carrying capacity $K$), and types mutate at rates $\theta^+/K$ ($+\to-$) and $\theta^-/K$ ($-\to+$). Let $W_K(t)$ be the fraction of type $-$ at time $Kt$ once the population has reached carrying capacity.

**Theorem.** Assume $W_K(0) \Rightarrow W_0$ and $\sup_K\sum_i i^{2+\eta}\mu^\pm_K(i) < \infty$ for some $\eta > 0$. Then $W_K$ converges weakly to the unique strong solution of the Gillespie–Wright–Fisher SDE

$$\begin{aligned}
dW &= -\big[(\mathfrak s^+ - \mathfrak v^+) - (\mathfrak s^- - \mathfrak v^-)\big]W(1-W)\,dt + \big[\theta^+(1-W) - \theta^-W\big]dt\\
&\quad + \sqrt{\big(\mathfrak m + \mathfrak v^+W + \mathfrak v^-(1-W)\big)W(1-W)}\;dB_t,
\end{aligned}$$

so the squared noise coefficient is $(\mathfrak m + \mathfrak v^-)W(1-W) + (\mathfrak v^+ - \mathfrak v^-)W^2(1-W)$. The statement of the source's Theorem 2 prints a minus sign before the last term; the generator computed in its proof of Theorem 2 (end of Section 5) gives the plus sign used here, and only the plus sign is compatible with the drift and keeps the coefficient nonnegative.

If $\mathfrak v^+ = \mathfrak v^- = \mathfrak v$, $\mathfrak s^+ \ge \mathfrak s^-$ and $\theta^- = 0$, then $W$ is moment dual to the block-counting process $A$ of the ancestral selection graph,

$$\mathbb E\big[W(t)^n \mid W(0) = w\big] = \mathbb E\big[w^{A(t)} \mid A(0) = n\big],$$

where $A$ jumps $n \mapsto n-1$ at rate $\binom{n}{2}(\mathfrak m + \mathfrak v) + n\theta^+$ (coalescence or a mutation that kills the lineage) and $n \mapsto n+1$ at rate $n(\mathfrak s^+ - \mathfrak s^-)$ (selective branching). Under stochastic-ordering and moment conditions, the time-rescaled lineage-counting process of the ancestral selection graph of the finite population converges to this $A$.

## Expansion

At carrying capacity the total size stays near $K$, and the type frequency changes only through small differences in reproduction and death, so on time scale $K$ it is a diffusion. The variance of reproduction enters twice: as genetic drift, through $\mathfrak m + \mathfrak v$, and as an effective selection term (Gillespie's effect), since a type with more variable offspring numbers is disadvantaged by $\mathfrak v^\pm$ in the drift. Katzenberger's method for processes pushed onto an attracting set by a strong deterministic flow (here the logistic attraction to size $K$) gives the limit. Before carrying capacity is reached, the population is coupled to independent supercritical branching processes, whose type proportions at the end of growth set the initial condition $W_0$.

## Sources

- Marta Dai Pra and Julian Kern, "Multi-type logistic branching processes with selection: Frequency process and genealogy for large carrying capacities", Electron. J. Probab. 31 (2026), 1–39, <https://doi.org/10.1214/26-EJP1592>. Numbering follows the arXiv version, arXiv:2507.12601 (2025): Theorems 1, 2 and 3, <https://doi.org/10.48550/arXiv.2507.12601>.
