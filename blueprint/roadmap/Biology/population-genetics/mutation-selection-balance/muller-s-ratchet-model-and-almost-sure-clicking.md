# Almost-sure repeated clicking of a finite mutation ratchet

Fix an integer $N\ge1$, $0\le s<1$ and a finite real $U>0$.
Start with $N$ finite nonnegative integer mutation loads.
At each generation choose each offspring's parent independently with
probability proportional to $(1-s)^k$, where $k$ is the parent's load.
All these reproductive weights are positive.
Each offspring then acquires an independent $\operatorname{Poisson}(U)$
number of new mutations, independent of parent choices and the past.
There is no recombination, back mutation or compensatory mutation.

If $K_{\min}(t)$ is the smallest load, then it is nondecreasing and

$$\mathbb P\bigl(K_{\min}(t+1)>K_{\min}(t)
\text{ for infinitely many }t\bigr)=1.$$

In particular $K_{\min}(t)\to\infty$ almost surely. The result includes
$s=0$, where it describes neutral mutation accumulation.

## Background

- [Infinite-population Poisson mutation–selection equilibrium](multilocus-multiplicative-mutation-selection-poi.md)

## Expansion

Every offspring has at least its parent's load, proving pathwise
monotonicity. Conditional on any past, the event that **every** offspring
acquires at least one new mutation has probability
$\delta=(1-e^{-U})^N>0$. On that event the minimum increases by at least
one, regardless of which parents were sampled.
By iterated conditioning, the probability of no such event in any next
$m$ generations is $(1-\delta)^m$ (the upper bound alone suffices).
For each starting time this tends to zero. Taking a countable intersection
over starting times proves infinitely many such events, hence clicks.
This direct finite-block argument supplies the required probabilistic
step without an unexplained conditional Borel–Cantelli prerequisite.

Only for $0<s<1$, the linked **deterministic infinite-population** model
has the Poisson$(U/s)$ equilibrium, whose zero-load frequency is $e^{-U/s}$.
The quantity $Ne^{-U/s}$ is a benchmark expected class size, not a
stationary-law assertion for the finite ratchet: the latter's absolute
minimum diverges. The infinite-population equilibrium is Background,
not a premise of the finite theorem; no such equilibrium is claimed at
$s=0$. Quantitative click-rate asymptotics remain a separate problem.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VIII.8, "Muller's Ratchet" (an asexual population can never contain a load smaller than that of its least-loaded lines; the ratchet advances whenever the least-loaded class is lost).
