# Law identification for the SIR chain on any probability space

Let $(\Omega, P)$ be a measure space and let $T$ be a map from $\Omega$ to pairs of real sequences
whose law is the [clock law](clock-law.md): $T$ is almost everywhere measurable and its image
measure is the clock law, so $P$ is a probability measure. Let $\beta, \gamma \ge 0$, let $x_0$
be any [SIR state](sirstate.md) (the constraint $S_0 + I_0 \le N$ is not needed), and let $Q$ be
the [rate matrix of the SIR chain](rate-matrix.md): off the diagonal, $Q(x, y)$ is the sum of
$\beta S I / N$ if $y$ is the infection target of $x = (S, I)$ and of $\gamma I$ if $y$ is its
recovery target (with the targets of the [SIR chain](sir-channels.md); $0$ if $y$ is neither), and
$Q(x, x) = -(\beta S I / N + \gamma I)$, where $\beta S I / N$ is $0$ when $N = 0$ by the
convention $x / 0 = 0$.

Then under $P$ the random path $(X(t))_{t \ge 0}$ of the [SIR path](sir-path.md) driven by
$T(\omega) = (e_1, e_2)$ from $x_0$ has the same law, on the space of functions from $[0, \infty)$
to SIR states with the product σ-algebra, as the
[path](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
started at $x_0$ of the continuous-time Markov chain with rate matrix $Q$, built from a step
sequence with the
[i.i.d. step law](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md)
of $Q$.
