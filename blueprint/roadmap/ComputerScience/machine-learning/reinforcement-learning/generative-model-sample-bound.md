# Generative-model sample bound (restricted, non-minimax)

Let a finite discounted MDP have states $S$, actions $A$, discount $0 \le \gamma < 1$ and rewards in
$[0, 1]$. Draw $N$ independent next-state samples from $P(\cdot \mid s, a)$ for every pair and let
$\hat P$ be the empirical model. There is a universal constant $c$ such that, for $0 < \eta \le 2$ and
$0 < \delta < 1$, if $N \ge c\,(\lvert S \rvert + \log(\lvert S \rvert \lvert A \rvert / \delta))/\eta^2$, then with
probability at least $1 - \delta$ every pair has $\lVert \hat P(\cdot \mid s,a) - P(\cdot \mid s,a) \rVert_1 \le \eta$,
and on that event the optimal action-value functions satisfy
$\lVert \hat Q^* - Q^* \rVert_\infty \le \gamma\eta/(1-\gamma)^2$ by the simulation lemma (values lie in
$[0, 1/(1-\gamma)]$). This restricted bound has suboptimal dependence on $1-\gamma$ and is not the minimax
generative-model theorem; rewards in $[0, R_{\max}]$ multiply the value bound by $R_{\max}$.

## Depends on

- [Markov decision process](../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

- [Simulation lemma](simulation-lemma/stoch-value-sub-stoch-value-eq.md)

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and Algorithms*, monograph draft, Section 2.1: Proposition 2.1 (sample size $c\lvert S \rvert \log(c \lvert S \rvert \lvert A \rvert/\delta)/((1-\gamma)^4\epsilon^2)$ per pair gives $\ell_1$ model error $(1-\gamma)^2\epsilon$ and value error $\epsilon$) with the simulation lemma, Lemmas 2.2–2.3. The additive sample size above follows from Hoeffding's inequality over the $2^{\lvert S \rvert}$ events $\{s' \in B\}$ and a union bound over pairs; the factor $\gamma$ comes from $\lVert Q^* - \hat Q^* \rVert_\infty \le \gamma \lVert (P - \hat P) V^* \rVert_\infty/(1-\gamma)$. <https://rltheorybook.github.io/rltheorybook_ABJKS.pdf>
