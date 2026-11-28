# Group relative policy optimization

Group relative policy optimization (GRPO) replaces a learned value baseline by statistics of a group of responses to the same prompt. This folder covers the group-relative advantage and its zero-variance convention, the clipped GRPO objective, a policy improvement lower bound for the population objective, an off-policy reading of group-relative REINFORCE, and the gradient bias that response-dependent weights create on shared prefixes.

- [Group-relative advantage](group-relative-advantage.md)
- [GRPO clipped surrogate objective](grpo-clipped-surrogate-objective.md)
- [GRPO policy improvement lower bound](grpo-policy-improvement-lower-bound.md)
- [Group-relative REINFORCE as a gradient step on a consistency loss](group-relative-reinforce-as-a-loss-gradient.md)
- [Shared-prefix gradients under group weights](shared-prefix-gradients-under-group-weights.md)
