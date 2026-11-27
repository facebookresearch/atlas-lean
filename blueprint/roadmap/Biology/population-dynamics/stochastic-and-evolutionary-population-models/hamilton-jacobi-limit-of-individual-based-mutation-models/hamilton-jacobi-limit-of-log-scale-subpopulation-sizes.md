# Hamilton–Jacobi limit of log-scale subpopulation sizes in a birth–death–mutation model

**Model.** An asexual population carries a trait on the torus $\mathbb T=\mathbb R/\mathbb Z$, discretized on the grid $\mathcal X_K=\{i\delta_K:0\le i<1/\delta_K\}$. An individual with trait $x$ gives birth to a clone at rate $b(x)$, dies at rate $d(x)$, and gives birth to a mutant with trait $y\in\mathcal X_K$ at rate

$$p(x)\,\delta_K\log K\;G\bigl(\overline{y-x}\,\log K\bigr),$$

where $\overline z\in[-\tfrac12,\tfrac12)$ is $z$ modulo $1$. So mutations occur at rate close to $p(x)$ with steps of order $1/\log K$. Let $N^K_i(t)$ be the number of individuals with trait $i\delta_K$ and define the log-scale exponents

$$\beta^K_i(t)=\frac{\log N^K_i(t\log K)}{\log K}\qquad(\beta^K_i(t)=0\text{ if }N^K_i(t\log K)=0),$$

so that subpopulation $i$ has size $K^{\beta^K_i(t)}$ at time $t\log K$. Let $\widetilde\beta^K_t$ be the piecewise-linear interpolation of $(\beta^K_i(t))_i$ on $\mathbb T$.

**Assumptions.** $b,d,p$ are Lipschitz on $\mathbb T$ with $b>d$ and $p>0$ (every clone is supercritical); $G\ge0$ is continuous with $\int G=1$, finite exponential moments of all orders and monotone tails; $N^K_i(0)\ge K^{a_1}$ for some $a_1>0$; $K^{-a_2/4}\ll\delta_K\ll1/\log K$ for some $a_2<a_1$; and the initial exponents are Lipschitz in $i\delta_K$ with probability tending to $1$.

**Statement.** If $\widetilde\beta^K_0$ converges in probability, uniformly on $\mathbb T$, to a deterministic $\beta_0\in C(\mathbb T)$, then for every $T>0$, $\widetilde\beta^K$ converges in probability in the Skorokhod space $\mathbb D([0,T],C(\mathbb T))$ to the unique Lipschitz viscosity solution of

$$\partial_t\beta(t,x)=b(x)-d(x)+p(x)\int_{\mathbb R}G(h)\,e^{h\,\partial_x\beta(t,x)}\,\mathrm dh,\qquad \beta(0,\cdot)=\beta_0.$$

## Expansion

Without mutation each subpopulation is a supercritical branching process and $\beta$ grows at rate $b-d$; a subpopulation of size $K^{\beta(x)}$ also seeds trait $x+h/\log K$ at rate about $p(x)G(h)K^{\beta(x)}$, which on the $\log K$ scale feeds the neighbour at the exponential rate $e^{h\partial_x\beta}$. The proof proves tightness by controlling the discrete gradients $(\beta^K_{i+1}-\beta^K_i)/\delta_K$ through martingale and branching comparisons, then identifies every limit point as a viscosity sub- and supersolution and concludes by uniqueness. This derives directly from the individual-based model the Hamilton–Jacobi dynamics that the PDE theory of concentration in selection–mutation equations obtains only after a deterministic limit, without passing through large-population PDEs.

## Sources

- Nicolas Champagnat, Sylvie Méléard, Sepideh Mirrahimi and Viet Chi Tran, "Filling the gap between individual-based evolutionary models and Hamilton-Jacobi equations", Journal de l’École polytechnique — Mathématiques 10 (2023), 1247–1275, <https://doi.org/10.5802/jep.244>; numbering as in arXiv:2205.00770: Assumptions 2.1 and 2.2, Theorem 2.3 (main result), Theorems 2.4 and 2.5 (tightness and identification).
