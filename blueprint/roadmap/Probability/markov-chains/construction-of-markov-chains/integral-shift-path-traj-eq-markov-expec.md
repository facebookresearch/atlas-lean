# Integral of a shifted path functional

Let $S$ be a nonempty standard Borel space,
$\kappa$ a Markov kernel on $S$, and $Y : S^{\mathbb{N}} \to \mathbb{R}$ a bounded function,
measurable for the product $\sigma$-algebra. Fix $n \in \mathbb{N}$ and a history
$x = (x_0, \dots, x_n)$ of states in $S$, and let $P_{n,x}$ be the Ionescu–Tulcea trajectory
measure on $S^{\mathbb{N}}$ that equals $x$ at times $0, \dots, n$ and afterwards draws each
next state from $\kappa$ applied to the current state. Then

$$\int Y(\theta_n \omega) \, dP_{n,x}(\omega) = \int Y \, dP_{\delta_{x_n}},$$

where $(\theta_n \omega)_k = \omega_{n+k}$ is the time-$n$ shift and $P_{\delta_{x_n}}$ is the
law on path space of the Markov chain with transition kernel $\kappa$ and initial distribution
the Dirac measure at $x_n$.

The statement also takes a finite measure $\mu$ on $S$, which does not appear in it.
