# Test-count lower bound for nonadaptive group testing with heterogeneous infection priors

**Setting.** $N$ individuals are independently infected with prior probabilities $p_i\le\tfrac12$. A nonadaptive testing matrix $G$ with $T$ rows pools individuals; a pool tests positive iff it contains an infected member, and the infection vector is decoded from the outcomes. Let $P_e^*(G,\mathbf{p})$ be the minimal error probability achievable with $G$. A prior vector is **$\eta$-bounded** if $\max_ip_i/\min_ip_i\le\eta$.

**Theorem.**

*(1)* *(Monotonicity.)* Lowering one prior, $p'_j\le p_j\le\tfrac12$ with all other priors equal, cannot increase the optimal error: $P_e^*(G,\mathbf{p}')\le P_e^*(G,\mathbf{p})$. Hence $P_e^*(G,\mathbf{p}_{\max})\ge P_e^*(G,\mathbf{p})\ge P_e^*(G,\mathbf{p}_{\min})$ for the constant vectors at $\max_ip_i$ and $\min_ip_i$.

*(2)* *(Lower bound.)* Driving the error to $0$ as $N\to\infty$ requires

$$T=\Omega\big(\min\{N,\ N\,p_{\min}\log N\}\big).$$

If $\mathbf{p}$ is $\eta$-bounded for a constant $\eta$, then $T=\Omega(\min\{N,\,N\bar p\log N\})=\Omega(\min\{N,\,Np_{\max}\log N\})$, with $\bar p$ the mean prior.

*(3)* *(Daily testing under SIR community spread.)* In a discrete-time SIR stochastic block model with $N$ people in communities of size $C$, within- and between-community daily transmission probabilities $q_1,q_2$ and initial infection probability $p_{\rm init}$: if $p_{\rm init}\le\tfrac12$, $q_1\le(1-1/\sqrt2)/C$ and $q_2\le(1-1/\sqrt2)/N$, then every day's infection probabilities stay $\le\tfrac12$, and if $q_1/q_2\le\eta$ each day's prior vector is $\eta$-bounded. So identifying every new infection each day needs $\Omega(\min\{N,N\bar p_t\log N\})$ tests on day $t$, and this lower bound falls below $N$ (complete testing) only while daily infection probabilities are $o(1/\log N)$.

## Expansion

With priors at most $\tfrac12$, lowering a prior makes the unknown infection vector less random, and the optimal (MAP) error cannot grow; this reduces the heterogeneous problem to the homogeneous one at $p_{\min}$, for which, heuristically, the classical counting bound says $T$ tests can resolve at most $2^T$ outcomes while the entropy of the infection vector is about $Nh(p)\approx Np\log(1/p)$, giving the $Np\log N$ order. Community structure keeps the daily priors within a constant ratio, so the bound can be stated in terms of the mean infection probability, while the paper's dynamic testing schemes exploit community correlations to approach it.

## Sources

- Sundara Rajan Srinivasavaradhan, Pavlos Nikolopoulos, Christina Fragouli and Suhas Diggavi, "Dynamic group testing to control and monitor disease progression in a population", arXiv:2106.10765 (2021), Theorems 1–3 and Corollaries 1–2, including the definition of $\eta$-bounded priors, <https://doi.org/10.48550/arXiv.2106.10765>.
