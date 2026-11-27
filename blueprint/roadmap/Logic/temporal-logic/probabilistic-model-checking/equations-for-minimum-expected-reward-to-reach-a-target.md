# Equations for minimum expected reward to reach a target

Let $M$ be a [Markov decision process](markov-decision-processes-and-adversaries.md) with a [reward structure](reward-structures.md) $r$ and target set $T$, and let $S^1_{\max}$ be the set of states from which some adversary reaches $T$ with probability $1$. For the random variable $C^T_r$ that sums the rewards $r_{\mathrm{state}}(s_i) + r_{\mathrm{action}}(s_i, a_i)$ up to the first visit to $T$ (over the whole path if $T$ is never reached), suppose there is a *proper* adversary achieving its minimum, that is, an adversary $\sigma$ with $\Pr^\sigma_s(\mathit{reach}(T)) = 1$ and $E^\sigma_s(C^T_r) = E^{\min}_s(C^T_r)$ for all $s \in S^1_{\max}$. Then the [minimum expected cumulative rewards](expected-cumulative-reward-to-reach-a-target.md) $x_s = E^{\min}_s(F^T_r)$, $s \in S^1_{\max}$, are the unique solution in $[0, \infty)$, indexed by $S^1_{\max}$, of

$$x_s = \begin{cases} 0 & \text{if } s \in T, \\ r_{\mathrm{state}}(s) + \min_{a \in A(s)} \Bigl( r_{\mathrm{action}}(s, a) + \sum_{s' \in S} \delta_M(s, a)(s') \cdot x_{s'} \Bigr) & \text{otherwise,} \end{cases}$$

for $s \in S^1_{\max}$, where the sum ranges over the successors $s'$ with $\delta_M(s, a)(s') > 0$ and $x_{s'} = \infty$ for $s' \notin S^1_{\max}$, so that an action that can leave $S^1_{\max}$ contributes $\infty$ to the minimum; and $E^{\min}_s(F^T_r) = \infty$ for $s \notin S^1_{\max}$. Both restrictions matter: with zero rewards and a choice at $s$ between a self-loop and a move to the target, $x_s = \min(x_s, 0)$ also has the solution $-1$; and an action of reward $1$ that reaches $s$ or the target with probability $\tfrac12$ each gives $x_s = 1 + x_s/2$, solved by $2$ and by $\infty$. The existence of a proper adversary can be ensured by first removing end components that carry only zero rewards.

## Depends on

- [Expected cumulative reward to reach a target](expected-cumulative-reward-to-reach-a-target.md)
- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)
- [Reward structures](reward-structures.md)
- [End components](end-components.md)

## Proof depends on

- [Qualitative reachability by graph analysis](qualitative-reachability-by-graph-analysis.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 5.3 (the equations for $E^{\min}_s(F^T_r)$ under the proper-adversary assumption, after Bertsekas and Tsitsiklis and de Alfaro).
