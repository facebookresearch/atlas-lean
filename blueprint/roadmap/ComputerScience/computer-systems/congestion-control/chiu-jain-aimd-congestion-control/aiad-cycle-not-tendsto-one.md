# An AIAD orbit whose fairness does not converge to one

Consider synchronous additive-increase additive-decrease control for two users with goal $4$, increase $1$ and decrease $-1$ (truncated at zero), started from loads $(1, 2)$. The orbit alternates between $(1, 2)$ and $(2, 3)$: the total $3$ does not exceed the goal, so both loads increase, and the total $5$ does, so both decrease. The Jain fairness index $(x_1 + x_2)^2 / (2(x_1^2 + x_2^2))$ alternates between $9/10$ and $25/26$, so it does not tend to $1$.
