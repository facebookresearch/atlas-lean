# Positive predictive value

For a probability measure $\mu$ on $\{0,1\} \times \{0,1\}$,
the joint law of a binary label $Y$ and a binary prediction $\hat Y$ in a group (Lean's
`Bool × Bool`, with `true` for $1$; the first coordinate is $Y$), the positive predictive value
is $\mathrm{PPV} = \Pr(Y = 1 \mid \hat Y = 1)$, computed with the conditional probability measure
$\mu(\cdot \mid \hat Y = 1)$. When $\Pr(\hat Y = 1) = 0$ that measure is zero and the value is
$0$.

## Sources

- A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.1, Definition 2, equation (2.2) and the remark after it.
