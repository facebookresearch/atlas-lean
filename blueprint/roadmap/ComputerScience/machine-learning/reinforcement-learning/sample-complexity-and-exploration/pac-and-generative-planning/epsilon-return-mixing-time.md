# Epsilon-return mixing time

The $\varepsilon$-return mixing time of an ergodic policy is the first horizon after which its expected $T$-step average payoff stays within $\varepsilon$ of its asymptotic average payoff from every start state. It is the time scale against which polynomial bounds for undiscounted exploration are stated.

Let $M$ be a Markov decision process on states $1, \dots, N$ with actions $a_1, \dots, a_k$, transition probabilities $P^a_M(ij)$, and a payoff distribution at each state $i$ with mean $R_M(i) \in [0, R_{\max}]$ and variance at most $\mathrm{Var}_{\max}$ (payoffs are attached to states). A policy is a map $\pi$ from states to actions; it is ergodic when the Markov chain it induces has a well-defined stationary distribution. For $T \ge 1$, a $T$-path is a sequence $p = (i_1, \dots, i_{T+1})$ of states, traversed under $\pi$ from $i_1$ with probability $\Pr^\pi_M[p] = \prod_{k=1}^{T} P^{\pi(i_k)}_M(i_k i_{k+1})$, and its undiscounted return is $U_M(p) = (R_M(i_1) + \dots + R_M(i_T))/T$. The $T$-step undiscounted return of $\pi$ from $i$ is

$$U^\pi_M(i, T) = \sum_{p} \Pr^\pi_M[p]\, U_M(p),$$

summing over the $T$-paths that start at $i$, and $U^\pi_M = \lim_{T \to \infty} U^\pi_M(i, T)$ is its asymptotic return, which does not depend on $i$ when every policy is ergodic (unichain MDPs).

**Definition.** The $\varepsilon$-return mixing time of an ergodic policy $\pi$ is the smallest $T$ such that $|U^\pi_M(i, T') - U^\pi_M| \le \varepsilon$ for all $T' \ge T$ and all states $i$. The class $\Pi^{T,\varepsilon}_M$ consists of the ergodic policies whose $\varepsilon$-return mixing time is at most $T$, and $\mathrm{opt}(\Pi^{T,\varepsilon}_M)$ is the largest asymptotic undiscounted return of a policy in this class.

The notion is weaker than the usual mixing time of the state distribution: only the expected average payoff has to settle. For stochastic games the R-max analysis uses a one-sided adversarial variant, in which only shortfalls below the long-run value count and the bound must hold against every behaviour of the opponent; it is spelled out on the [fixed-sum stochastic game](fixed-sum-stochastic-game.md) page.

## Depends on

- [Markov decision process](../../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

None.

## Expansion

Kearns and Singh argue that, without further assumptions on the MDP or the policy, it is not reasonable to expect a learner to approach the asymptotic return of a policy in many fewer steps than its $\varepsilon$-return mixing time, which is why they state their undiscounted bounds in terms of $T$. Kearns and Singh illustrate this with a two-state, one-action chain: from a payoff-$0$ state the chain moves to an absorbing state of positive payoff with a small probability per step, so both the $\varepsilon$-return mixing time and the time needed to approach the asymptotic return are of the order of the expected waiting time.

## Sources

- M. Kearns and S. Singh, "Near-Optimal Reinforcement Learning in Polynomial Time", *Machine Learning* 49 (2002), 209–232, doi:10.1023/A:1017984413808: Definitions 1–6 (Section 2 and Section 3, pp. 211–215).
