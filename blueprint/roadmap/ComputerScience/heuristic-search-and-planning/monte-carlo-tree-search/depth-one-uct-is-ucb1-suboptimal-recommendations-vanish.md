# Depth-one UCT is UCB1; suboptimal recommendations vanish

Consider a single decision node with $K \ge 2$ actions whose payoffs are independent across plays,
i.i.d. per action and supported in $[0,1]$, with means $\mu_a$, best mean $\mu^*$ and gaps
$\Delta_a = \mu^* - \mu_a$. UCT at this node, which first plays each action once and then plays an action
maximizing $\bar X_a + 2 C_p \sqrt{\ln t / s_a}$, where $t$ is the number of plays so far and $s_a$ the number of
plays of $a$, with $C_p = 1/\sqrt 2$, is exactly UCB1 with index
$\bar X_a + \sqrt{2 \ln t / s_a}$, with the same initialization and tie rule; hence the expected number of
plays of every suboptimal action satisfies the UCB1 bound. As a separate corollary, after $n \ge K$
plays the most-played action is suboptimal with probability at most
$\sum_{a : \Delta_a > 0} K\, \mathbb{E}[T_a(n)]/n$ (if a suboptimal action is most played, it has at least
$n/K$ plays; apply Markov's inequality), which tends to $0$. This is a statement about one decision node,
not consistency of multilevel UCT.

The corollary is an elementary consequence, not a statement of the cited sources.

## Depends on

- [UCT Monte-Carlo tree search](uct-monte-carlo-tree-search.md)

## Proof depends on

- [Pull-count bound for UCB1](../../machine-learning/reinforcement-learning/multi-armed-bandits/pull-count-bound-for-ucb1.md)

## Related topics

- [Anytime regret bound for UCB1](../../machine-learning/reinforcement-learning/multi-armed-bandits/anytime-regret-bound-for-ucb1.md)

## Sources

- L. Kocsis and Cs. Szepesvári, *Bandit based Monte-Carlo planning*, ECML 2006, LNCS 4212, 282–293: equations (1)–(2) and the proof of Theorem 6, where depth one is UCB1 with $C_p = 1/\sqrt 2$. <https://sites.ualberta.ca/~szepesva/papers/ecml06.pdf>
- P. Auer, N. Cesa-Bianchi and P. Fischer, *Finite-time analysis of the multiarmed bandit problem*, Machine Learning 47 (2002) 235–256, Figure 1 (UCB1) and Theorem 1, with the bound on $\mathbb{E}[T_j(n)]$ from its proof. <https://homes.di.unimi.it/~cesa-bianchi/Pubblicazioni/ml-02.pdf>
