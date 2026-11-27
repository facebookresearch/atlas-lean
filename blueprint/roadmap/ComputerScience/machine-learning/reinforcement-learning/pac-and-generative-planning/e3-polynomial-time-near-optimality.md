# E3 attains near-optimal return in polynomial time

The E3 algorithm reaches near-optimal return in a number of actions and an amount of computation polynomial in the number of states, $1/\varepsilon$, $1/\delta$, the payoff bound and the mixing time (undiscounted case) or horizon time (discounted case), with probability at least $1-\delta$.

**Theorem.** Let $M$ be a Markov decision process over $N$ states with a constant number of actions, payoff means in $[0, R_{\max}]$ attached to states and payoff variances bounded by a constant $\mathrm{Var}_{\max}$.

- *(Undiscounted case.)* Let $\Pi^{T,\varepsilon}_M$ be the class of ergodic policies whose $\varepsilon$-return mixing time is at most $T$ and $\mathrm{opt}(\Pi^{T,\varepsilon}_M)$ the optimal asymptotic expected undiscounted return in this class. There is an algorithm $A$, taking inputs $\varepsilon$, $\delta$, $N$, $T$ and $\mathrm{opt}(\Pi^{T,\varepsilon}_M)$, whose total number of actions and computation time are polynomial in $1/\varepsilon$, $1/\delta$, $N$, $T$ and $R_{\max}$, and such that with probability at least $1-\delta$ the total actual return of $A$ exceeds $\mathrm{opt}(\Pi^{T,\varepsilon}_M) - \varepsilon$.
- *(Discounted case.)* Let $V^*(i)$ be the optimal expected discounted return from state $i$. There is an algorithm $A$, taking inputs $\varepsilon$, $\delta$, $N$ and $V^*(i)$, whose total number of actions and computation time are polynomial in $1/\varepsilon$, $1/\delta$, $N$, the horizon time $T = 1/(1-\gamma)$ and $R_{\max}$, and such that with probability at least $1-\delta$ it halts in a state $i$ and outputs a policy $\hat\pi$ with $V^{\hat\pi}_M(i) \ge V^*(i) - \varepsilon$.

The source's proof constructs $A$ from the E3 algorithm, with a known-state visit threshold chosen so that the conclusion of its Lemma 5 holds: except with probability $\delta/(3N)$ per state, the estimated transition probabilities and payoff mean of each known state are within $O((\varepsilon/(N T G^T_{\max}))^2)$ of their true values. In the undiscounted case it runs E3 with the input $T$ used as the $\varepsilon/2$-return mixing time. The undiscounted statement assumes a unichain MDP (every policy ergodic); the inputs $\mathrm{opt}(\Pi^{T,\varepsilon}_M)$, $V^*(i)$ and $T$ can be removed without leaving polynomial time.

## Depends on

- [Explicit Explore or Exploit algorithm](explicit-explore-or-exploit-algorithm.md)
- [Epsilon-return mixing time](epsilon-return-mixing-time.md)

## Proof depends on

- [Explore or Exploit Lemma](explore-or-exploit-lemma.md)
- [Epsilon-horizon time truncation](epsilon-horizon-time-truncation.md)
- [The dynamic programming policy attains the value iterate](../../../heuristic-search-and-planning/optimality-of-stationary-policies/n-stage-value-dp-policy.md)
- [Multiplicative Chernoff bounds](../../../../Probability/concentration-inequalities/chernoff-and-bernoulli-comparison-bounds/multiplicative-chernoff-bounds.md)
- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)

## Expansion

The source allots probability $\delta/3$ to each of three failure sources. First, a known state may be poorly estimated: the source's simulation lemma (estimates within $O((\varepsilon/(N T G^T_{\max}))^2)$ of the truth, payoff errors included, give $T$-step returns within $\varepsilon$, with the horizon truncation in the discounted case) is applied with a per-state failure probability $\delta/(3N)$. Second, the Explore or Exploit Lemma, transferred from the estimated to the true known-state MDP, shows that each attempted exploration reaches an unknown state with probability at least $\varepsilon/(2G^T_{\max})$; enough attempted explorations then produce the at most $N m_{\mathrm{known}}$ steps of balanced wandering after which every state is known. In the undiscounted case the simulation lemma is stated for policies whose $\varepsilon/2$-return mixing time is $T$, while the theorem competes with $\Pi^{T,\varepsilon}_M$; the source bridges the two by its note 1, which asserts that the $\varepsilon/2$- and $\varepsilon$-return mixing times are linearly related by standard eigenvalue arguments, without proof. Third, in the undiscounted case exploitation blocks of expected return $\mathrm{opt} - \varepsilon/2$ must realize their return and outweigh the exploration blocks, which multiplies the number of actions by a factor of order $T/\varepsilon$. $T$-step value iteration on the partial model computes the optimal $T$-step policies the algorithm uses. The source treats successive attempts as independent trials; since they are chosen adaptively, a martingale form of the tail bound is the rigorous tool. The source remarks that no attempt was made to optimize the resulting polynomials; for discounted MDPs the PAC-MDP analysis of R-max gives explicit bounds.

## Sources

- M. Kearns and S. Singh, "Near-Optimal Reinforcement Learning in Polynomial Time", *Machine Learning* 49 (2002), 209–232, doi:10.1023/A:1017984413808: Theorem 3 (Main Theorem, Section 5, pp. 216–217), its proof in Sections 5.2–5.5 including equations (45)–(49) (pp. 218–228), Section 6 (removing the inputs), Section 7 (multichain MDPs) and note 1 (p. 230).
