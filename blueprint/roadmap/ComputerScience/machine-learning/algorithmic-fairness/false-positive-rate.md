# False-positive rate

For a probability measure $\mu$ on $\{0,1\} \times \{0,1\}$, the
joint law of a binary label $Y$ and a binary prediction $\hat Y$ in a group (Lean's
`Bool × Bool`, with `true` for $1$; the first coordinate is $Y$), the false-positive rate is
$\mathrm{FPR} = \Pr(\hat Y = 1 \mid Y = 0)$, computed with the conditional probability measure
$\mu(\cdot \mid Y = 0)$. When $\Pr(Y = 0) = 0$ that measure is zero and the rate is $0$.

## Sources

- A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.1, Definition 3, equation (2.3).
