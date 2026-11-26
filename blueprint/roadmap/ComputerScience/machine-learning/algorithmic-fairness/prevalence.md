# Prevalence

For a probability measure $\mu$ on $\{0,1\} \times \{0,1\}$, the joint law of
a binary label $Y$ and a binary prediction $\hat Y$ in a group (Lean's `Bool × Bool`, with `true`
for $1$; the first coordinate is $Y$), the prevalence of the group is $p = \Pr(Y = 1)$, the
$\mu$-probability of the event $\{Y = 1\}$.

## Sources

- A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.3 (the recidivism prevalence $P(Y = 1 \mid R = r)$ of group $r$).
