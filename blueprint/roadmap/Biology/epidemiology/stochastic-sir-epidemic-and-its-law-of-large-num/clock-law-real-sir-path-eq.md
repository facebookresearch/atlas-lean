# Transition probabilities of the SIR chain

Let $\beta, \gamma \ge 0$, let $x_0$ and $j$ be [SIR states](sirstate.md) (the constraint
$S_0 + I_0 \le N$ is not needed) and let $t \ge 0$. Let $Q$ be the
[rate matrix of the SIR chain](rate-matrix.md): off the diagonal, $Q(x, y)$ is the sum of
$\beta S I / N$ if $y$ is the infection target of $x = (S, I)$ and of $\gamma I$ if $y$ is its
recovery target (with the targets of the [SIR chain](sir-channels.md); $0$ if $y$ is neither), and
$Q(x, x) = -(\beta S I / N + \gamma I)$, where $\beta S I / N$ is $0$ when $N = 0$ by the
convention $x / 0 = 0$. Under the [clock law](clock-law.md) $\mathbb{P}$
(independent rate-1 exponential interarrival times),

$$\mathbb{P}\bigl(X(t) = j\bigr) = e^{tQ}(x_0, j),$$

where $X$ is the [SIR path](sir-path.md) driven by $(e_1, e_2)$ from $x_0$ and $e^{tQ}$ is the
[transition function](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md)
of $Q$, a matrix exponential.
