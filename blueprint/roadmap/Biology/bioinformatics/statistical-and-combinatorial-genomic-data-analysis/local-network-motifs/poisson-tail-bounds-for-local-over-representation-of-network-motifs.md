# Poisson tail bounds for local over-representation of network motifs

**Setting.** Let $G$ be a random (directed) graph on $n$ vertices with independent edges whose probabilities are given by the model (e.g. a mixture or degree-based model). Fix a pattern $m$ on $k$ vertices, a **deletion class** $C$ of $m$ (an orbit of its automorphism group) and the **subpattern** $m'$ obtained by deleting a vertex of $C$. For a position $U$ (an ordered vertex set) with $G[U] \cong m'$, let $N_U$ be the number of vertices $v \notin U$ such that $G[U \cup \{v\}] \cong m$ with $v$ playing the role of $C$ (the order of the $(m,C)$-**theme** at $U$). Given $G[U] \cong m'$, the indicators $I_U^v$ are independent with probabilities $p_U^v$; set $\lambda_U = \sum_{v\notin U}p_U^v = \mathbb E[N_U \mid G[U] \cong m']$ and $\Delta_U = (N_U - \lambda_U)/\lambda_U$.

**Theorem (local bound).** With $t_\lambda = 1 + \frac{1}{4\pi\lambda}\big(1 + \sqrt{1 + 16\pi\lambda}\big)$ and

$$h(\lambda,t) = \begin{cases} 1, & t \le t_\lambda,\\ \dfrac{\sqrt{t+1}}{\sqrt{2\pi\lambda}\,(t-1)}, & t > t_\lambda,\end{cases}$$

for every $t > 0$

$$\mathbb P(\Delta_U \ge t) \le \mathbb P(G[U] \cong m')\,h(\lambda_U,t)\,e^{-\lambda_U((1+t)\ln(1+t) - t)}.$$

**Theorem (global statistic).** Let $g(\lambda,t) = \lambda((1+t)\ln(1+t) - t) - \ln h(\lambda,t)$, an increasing bijection of $(0,\infty)$ in $t$ with $g(\lambda,t) \sim \lambda t\ln t$. If $N(m')$ is the total number of occurrences of $m'$ in $G$, then for every $t > 0$

$$\mathbb P\Big(\max_U g(\lambda_U, \Delta_U) \ge t\Big) \le \mathbb E[N(m')]\,e^{-t}.$$

Thus $\max_U g(\lambda_U,\Delta_U)$ is a single test statistic for a **local motif** (a theme of surprisingly large order somewhere in the network) whose $p$-value is bounded without simulation; matching lower bounds show the tail estimate is sharp under sparsity conditions on the edge probabilities.

## Proof sketch

Conditionally on the core $U$, $N_U$ is a sum of independent Bernoulli variables, so Chen–Stein Poisson approximation (Barbour–Holst–Janson) controls its upper tail for large deviations, and a Bennett/McDiarmid-type concentration inequality gives the bound $e^{-\lambda((1+t)\ln(1+t) - t)}$ for moderate deviations; $h$ selects the sharper of the two. Transforming by $g$ makes every position's tail at most $e^{-t}$ times the probability that $U$ hosts the subpattern, so a union bound over positions costs exactly the expected number of subpattern occurrences, solving the multiple-testing problem. In regulatory networks this detects, e.g., transcription factor pairs that jointly regulate unusually many targets.

## Sources

- Etienne Birmelé, "Detecting local network motifs", *Electronic Journal of Statistics* 6 (2012), 908–933, <https://doi.org/10.1214/12-ejs698>. Preprint version: arXiv:1007.1410 (2010), Section 2 (themes, deletion classes, Theorems 2.1–2.2) and Section 3 (Propositions 3.1–3.2), <https://doi.org/10.48550/arXiv.1007.1410>.
