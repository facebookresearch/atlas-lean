# State distribution in a discrete-time multistate life table

Let $S$ be a finite state set containing a nonempty set of absorbing death states ($P_x(d, d) = 1$ for every death state $d$ and age $x$), and let $P_0, P_1, \dots$ be row-stochastic matrices on $S$, one for each integer age interval $[x, x+1)$, so the chain may be time-inhomogeneous. For a Markov chain $(Z_x)$ with these transition matrices and initial law $\pi_0$ (a row vector), the law of $Z_x$ is $\pi_x = \pi_0P_0P_1\cdots P_{x-1}$, the product taken in age order; matrices for different ages need not commute. Mass in the death states never decreases. Migration in and out of the cohort, observation at non-integer ages and continuous-time transition intensities are outside this statement.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Law of a time-inhomogeneous finite Markov chain at time $x$ as the ordered product of its transition matrices.

## Sources

- J. Ledent, *An Improved Methodology for Constructing Increment-Decrement Life Tables from the Transition Perspective*, IIASA Working Paper WP-80-104, 1980, discussion of equation (4), <http://pure.iiasa.ac.at/id/eprint/1365/1/WP-80-104.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
