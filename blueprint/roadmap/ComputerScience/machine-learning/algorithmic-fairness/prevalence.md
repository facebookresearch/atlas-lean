# Prevalence

For a measure $\mu$ on $\{0,1\} \times \{0,1\}$ (Lean's `Bool × Bool`, with
`true` for $1$), write $Y$ for the first coordinate and $\hat Y$ for the second. The prevalence of
$\mu$ is the real number $\mu(\{Y = 1\})$, the mass of the event $\{Y = 1\}$, taken as $0$ when
that mass is infinite. When $\mu$ is a probability measure, the joint law of a binary label $Y$
and a binary prediction $\hat Y$ in a group, it is the prevalence $p = \Pr(Y = 1)$ of the group.

## Sources

- A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.3 (the recidivism prevalence $P(Y = 1 \mid R = r)$ of group $r$).
