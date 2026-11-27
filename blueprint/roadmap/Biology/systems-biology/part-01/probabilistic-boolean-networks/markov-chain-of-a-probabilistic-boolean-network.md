# Markov chain of a probabilistic Boolean network

**Setting.** A Boolean network (BN) on genes $x_1, \dots, x_n$ is a map $f : \{0,1\}^n \to \{0,1\}^n$ updated synchronously, $x(t+1) = f(x(t))$. A probabilistic Boolean network (PBN) consists of $r$ BNs $f^{(1)}, \dots, f^{(r)}$ with selection probabilities $c_1, \dots, c_r$ ($c_k > 0$, $\sum_k c_k = 1$) and a gene-perturbation rate $p \in [0, 1)$. At each step, with probability $(1-p)^n$ no gene is perturbed and the state is updated by a network $f^{(k)}$ chosen with probability $c_k$; otherwise a nonzero random vector $\gamma \in \{0,1\}^n$ with independent $\Pr\{\gamma_i = 1\} = p$ flips the corresponding genes, $x \mapsto x \oplus \gamma$. (When networks are chosen independently at every step, the network-switching probability does not enter the transition law.)

**Statement.** The state process is a homogeneous Markov chain on $\{0,1\}^n$ with transition matrix

$$T = \bar T + \tilde T, \qquad \bar T = (1-p)^n \sum_{k=1}^r c_k T_k, \qquad \tilde T_{s,w} = p^{\eta(s,w)} (1-p)^{n - \eta(s,w)} \, \mathbf{1}[s \ne w],$$

where $T_k$ is the $0/1$ transition matrix of $f^{(k)}$ ($T_k(s, w) = 1$ iff $w = f^{(k)}(s)$) and $\eta(s,w)$ is the Hamming distance. Rows of $T$ sum to $1$, and $T$ can be assembled in $O(n\, r\, 2^n)$ operations.

1. *Deterministic case* ($r = 1$, $p = 0$). Every trajectory enters an attractor (a fixed point or a cycle) and the basins partition $\{0,1\}^n$. Any probability vector that is uniform on each attractor cycle and zero off the attractors is stationary; the stationary distribution is unique iff there is exactly one attractor, and the chain converges to it from every initial law iff that attractor is a single fixed point.
2. *Perturbed case* ($0 < p < 1$). All off-diagonal entries of $T$ are positive, so the chain is irreducible and has a unique stationary distribution $\pi$ ($\pi T = \pi$, $\sum_s \pi(s) = 1$). For $n \ge 2$ it is also aperiodic, hence ergodic: the distribution at time $t$ converges to $\pi$ from every initial condition. (For $n = 1$ the negation network gives a chain of period $2$, which still has a unique stationary law.)

## Expansion

A transition $s \to w$ happens either by the network update (probability $(1-p)^n c_k$ for $w = f^{(k)}(s)$) or by perturbation, where the specific flip pattern $\gamma = s \oplus w \ne 0$ has probability $p^{\eta}(1-p)^{n-\eta}$; summing over $\eta \ge 1$ with $\binom{n}{\eta}$ patterns gives $1 - (1-p)^n$, so rows sum to one. In the deterministic case the chain moves along the functional graph of $f$, a cycle of length $L$ supports the uniform law on it (stationary but periodic), and mixtures over attractors give all stationary laws. With $p > 0$ every state reaches every other in one step; with at least $4$ states there are closed walks of lengths $2$ and $3$ through any state, so the period is $1$. The source uses $\pi$ to define long-run attractor probabilities, which are the natural model counterparts of phenotype frequencies.

## Sources

- Y. Xiao, "A tutorial on analysis and simulation of Boolean gene regulatory network models", Current Genomics 10 (2009), 511–525, Section 2 (Definitions 1–4, Remark 1) and Section 3.1 (Eqs. (5)–(8), Definitions 5–6, stationary and steady-state distributions), <https://doi.org/10.2174/138920209789208237> (PMC2808677).
- I. Shmulevich, E. R. Dougherty, S. Kim, W. Zhang, "Probabilistic Boolean networks: a rule-based uncertainty model for gene regulatory networks", Bioinformatics 18 (2002), 261–274, <https://doi.org/10.1093/bioinformatics/18.2.261>.
