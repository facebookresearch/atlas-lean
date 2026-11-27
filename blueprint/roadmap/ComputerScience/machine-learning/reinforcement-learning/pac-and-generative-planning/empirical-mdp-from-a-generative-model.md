# Empirical MDP from a generative model

A generative model of an MDP returns, for any queried state-action pair, an independent next state drawn from its transition distribution. Querying it $N$ times per pair and normalizing the counts gives the empirical (plug-in) MDP, on which model-based planning is run.

Let $M = (S, A, P, r, \gamma)$ be a discounted MDP with finite state and action sets, transition kernel $P(\cdot \mid s, a)$, a known deterministic reward $r : S \times A \to [0, 1]$ and discount $\gamma \in [0, 1)$.

**Definition.** A generative model (simulator) for $M$ is an oracle that, given any pair $(s, a)$, returns a sample $s' \sim P(\cdot \mid s, a)$, independently of all previous calls. For an integer $N \ge 1$, calling it $N$ times at every pair yields samples $s^1_{s,a}, \dots, s^N_{s,a}$, a total of $N|S||A|$ calls, and the empirical transition kernel

$$\hat P(s' \mid s, a) = \frac{1}{N}\sum_{i=1}^N \mathbf 1\{s^i_{s,a} = s'\}.$$

The empirical MDP is $\hat M = (S, A, \hat P, r, \gamma)$; its values are written $\hat V^\pi$, $\hat Q^\pi$, its optimal values $\hat V^\star$, $\hat Q^\star$ and an optimal deterministic stationary policy of it $\hat\pi^\star$.

**Matrix notation.** $P$ is also read as the $(S \times A) \times S$ matrix with entries $P(s' \mid s, a)$, so $(PV)(s, a) = \sum_{s'}P(s' \mid s, a)V(s')$. For a deterministic stationary policy $\pi$, $P^\pi$ is the transition matrix on state-action pairs with $P^\pi_{(s,a),(s',a')} = P(s' \mid s, a)$ if $a' = \pi(s')$ and $0$ otherwise, so that $Q^\pi = r + \gamma PV^\pi = r + \gamma P^\pi Q^\pi$ and $Q^\pi = (I - \gamma P^\pi)^{-1}r$. For $V : S \to \mathbb R$ the one-step variance is the vector $\mathrm{Var}_P(V)(s, a) = \sum_{s'}P(s' \mid s, a)V(s')^2 - ((PV)(s, a))^2$. Square roots, squares and absolute values of vectors act entrywise, and $\mathbf 1$ is the all-ones vector.

**Correctness.** An algorithm that outputs $Q^{\mathcal A} : S \times A \to \mathbb R$ is $(\varepsilon, \delta)$-correct on a class of MDPs if $\|Q^* - Q^{\mathcal A}\|_\infty \le \varepsilon$ with probability at least $1-\delta$ for every MDP in the class; a policy $\pi$ is $\varepsilon$-optimal if $V^\pi(s) \ge V^*(s) - \varepsilon$ for every $s$.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Value of a policy](../../../heuristic-search-and-planning/value-iteration/policy-value.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)

## Proof depends on

None.

## Expansion

Values satisfy $0 \le V^\pi \le 1/(1-\gamma)$, so accuracies are meaningful for $\varepsilon \in (0, 1/(1-\gamma)]$. When rewards are unknown or random, a lower-order number of extra samples estimates them, so the reward is usually taken as known. The empirical kernel has at most $N|S||A|$ nonzero entries, which makes planning in $\hat M$ cheap when $N$ is small. A restricted non-minimax accuracy bound for this model, through an $\ell_1$ estimate of $\hat P$ and the simulation lemma, is the [generative-model sample bound](../generative-model-sample-bound.md); variance-aware arguments give the minimax rates.

## Sources

- M. G. Azar, R. Munos and H. J. Kappen, "Minimax PAC bounds on the sample complexity of reinforcement learning with a generative model", *Machine Learning* 91 (2013), 325–349, doi:10.1007/s10994-013-5368-1: Section 2 (Assumption 1, p. 328), Section 2.1 and Algorithm 3 (pp. 329–330), Definition 1 (p. 331).
- A. Agarwal, S. Kakade and L. F. Yang, "Model-Based Reinforcement Learning with a Generative Model is Minimax Optimal", *Proceedings of the Thirty Third Conference on Learning Theory*, PMLR 125 (2020), 67–83, [proceedings.mlr.press](https://proceedings.mlr.press/v125/agarwal20b.html): Section 2 (setting, generative model and empirical model) and the notation of Section 4.
