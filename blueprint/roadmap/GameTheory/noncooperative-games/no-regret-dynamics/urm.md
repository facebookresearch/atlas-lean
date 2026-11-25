# Unconditional regret matching

Let $A$ be a finite set of actions. Given a vector $x \in \mathbb R^A$ (the average regret vector), unconditional
regret matching gives each action $k$ the weight $x_k^+ / \sum_l x_l^+$, proportional to the positive part of its
regret, when some regret is positive, and the uniform weight $1/|A|$ otherwise (where Hart leaves the choice
arbitrary). For a nonempty $A$ these weights form a mixed action; for an empty $A$ there is nothing to play.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §3, Theorem B.
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §10.1.
