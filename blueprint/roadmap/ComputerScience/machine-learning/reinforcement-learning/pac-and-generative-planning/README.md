# PAC exploration and generative planning

Sample-efficient exploration in unknown MDPs (explicit and implicit explore-or-exploit, R-max, the PAC-MDP framework) and minimax sample complexity of planning with a generative model (variance techniques, absorbing-state decoupling, upper and lower bounds). The planning pages define the empirical MDP built from generative-model samples where they use it, and write $P^\pi$ for the transition matrix of a stationary policy on state-action pairs and $\mathrm{Var}_P(V)$ for one-step variances, each stating the notation it uses.

## Explore or exploit

- [Epsilon-return mixing time](epsilon-return-mixing-time.md)
- [Epsilon-horizon time truncation](epsilon-horizon-time-truncation.md)
- [Known-state MDP](known-state-mdp.md)
- [Explore or Exploit Lemma](explore-or-exploit-lemma.md)
- [Explicit Explore or Exploit algorithm](explicit-explore-or-exploit-algorithm.md)
- [E3 attains near-optimal return in polynomial time](e3-polynomial-time-near-optimality.md)
- [Fixed-sum stochastic game](fixed-sum-stochastic-game.md)
- [R-max algorithm](r-max-algorithm.md)
- [Simulation lemma for T-step average returns](simulation-lemma-for-t-step-average-returns.md)
- [Implicit Explore or Exploit Lemma](implicit-explore-or-exploit-lemma.md)
- [R-max attains near-optimal average reward in polynomial time](r-max-polynomial-time-near-optimality.md)

## PAC-MDP analysis

- [Sample complexity of exploration](sample-complexity-of-exploration.md)
- [PAC-MDP theorem for optimistic greedy algorithms](pac-mdp-theorem-for-optimistic-algorithms.md)
- [Sample complexity of exploration of R-max](r-max-sample-complexity-of-exploration.md)

## Planning with a generative model

- [Generative model of an MDP](generative-model-of-an-mdp.md)
- [Bellman equation for the return variance](bellman-equation-for-the-return-variance.md)
- [Total-variance bound](total-variance-bound.md)
- [Sample bound for model-based Q-value iteration](model-based-q-value-iteration-sample-bound.md)
- [Lower bound for estimating optimal action values](generative-model-lower-bound-for-optimal-q.md)
- [Variance-reduced Q-value iteration](variance-reduced-q-value-iteration.md)
- [Absorbing-state MDP lemma](absorbing-state-mdp-lemma.md)
- [Decoupled Bernstein bound for empirical optimal values](decoupled-bernstein-bound-for-empirical-values.md)
- [Plug-in planning with a generative model is minimax optimal](plug-in-planning-is-minimax-optimal.md)
- [Perturbed model-based planning attains the minimax rate for every accuracy](perturbed-model-based-planning.md)

## Related topics

- [Generative-model sample bound (restricted, non-minimax)](../generative-model-sample-bound.md)
- [Simulation lemma](../simulation-lemma/README.md)
- [Value iteration](../../../heuristic-search-and-planning/value-iteration/README.md)
