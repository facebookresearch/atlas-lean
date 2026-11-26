# Value of a nonanticipating stopping rule

On a binary tree with real branch weight $p$ and real discount $\delta$, for an exercise payoff $g$ on histories and a stopping rule that decides from the history $s$ and the number $k$ of periods left whether to exercise now, the value of the rule is $g(s)$ when $k = 0$ (exercise is forced at the horizon), and otherwise $g(s)$ if the rule exercises at $(k, s)$ and the continuation value of the rule with $k - 1$ periods left if it does not. For $p \in [0, 1]$ and $\delta \ge 0$ it is the discounted expected payoff of the rule.
