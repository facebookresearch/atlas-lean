# Strategy-proof matching mechanism

Let $M$ (the men) and $W$ (the women) be sets. A preference profile gives every man a strict total order of preference on $W$ and every woman one on $M$; a perfect matching is a bijection $\mu : M \to W$, and it is stable for a profile if no man $m$ and woman $w$ prefer each other to their partners.
A matching mechanism $h$ is strategy-proof when truthful revelation is a dominant strategy for every man and
every woman: for every stated profile and every agent, replacing that agent's preference by any other
strict order never yields a partner that the agent prefers, under the original preference, to the partner
obtained by stating it.

Unlike a social choice function, a matching mechanism gives each agent a private outcome (a partner), and
each agent judges outcomes by its preference over the other side.

## Background

- [Strategy-proof social choice function](../../social-choice/gibbard-satterthwaite-theorem/is-strategy-proof.md): the corresponding notion for social choice functions, where every voter ranks the same set of outcomes.

## Sources

- A. E. Roth, "The economics of matching: stability and incentives", *Mathematics of Operations Research* 7(4) (1982), 617–628, §4, the definition before Theorem 3 and footnote 10.
