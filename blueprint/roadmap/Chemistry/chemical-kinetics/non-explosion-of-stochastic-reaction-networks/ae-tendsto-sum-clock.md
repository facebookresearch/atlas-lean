# Almost surely the partial sums of the clocks tend to infinity

Let $S$ be a set with a σ-algebra, $P$ a jump kernel on $S$ (a probability mass function
$P(x, \cdot)$ on $S$ for each $x \in S$), and $\mathbb{P}_P$ the [input law](input-measure.md) on
step sequences $\omega = ((\xi_k, E_k))_{k \in \mathbb{N}}$. For $\mathbb{P}_P$-almost every
$\omega$,

$$E_0 + E_1 + \dots + E_{n-1} \to \infty \qquad (n \to \infty).$$

Under the input law the clocks are independent, each with the
[rate-one exponential law](input-measure-map-clock.md) of mean $1$, so this follows from the strong
law of large numbers.
