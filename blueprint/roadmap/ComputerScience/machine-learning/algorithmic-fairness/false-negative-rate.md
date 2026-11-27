# False-negative rate

For a measure $\mu$ on $\{0,1\} \times \{0,1\}$ (Lean's
`Bool × Bool`, with `true` for $1$), write $Y$ for the first coordinate and $\hat Y$ for the
second. The false-negative rate of $\mu$ is the real number $\mu(\{\hat Y = 0\} \mid Y = 1)$, the
mass of $\{\hat Y = 0\}$ under the conditional measure
$\mu(\cdot \mid Y = 1) = \mu(\{Y = 1\})^{-1} \, \mu(\cdot \cap \{Y = 1\})$; that measure is zero,
and the rate $0$, when $\mu(\{Y = 1\})$ is $0$ or infinite. When $\mu$ is a probability measure,
the joint law of a binary label $Y$ and a binary prediction $\hat Y$ in a group, the rate is
$\mathrm{FNR} = \Pr(\hat Y = 0 \mid Y = 1)$, which is $0$ when $\Pr(Y = 1) = 0$.

## Sources

- A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.1, Definition 3, equation (2.4).
