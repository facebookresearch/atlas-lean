# One step of the tabulated CRF forward algorithm

Let $c$ be a chain CRF with states
$\{0, \dots, n-1\}$ and weights in a semiring $R$ carrying a relation $\le$, with unary
potential $\phi_t(s)$ at position $t$ and transition potential $\psi_t(s', s)$ from $s'$ to $s$
at step $t$, given the observation sequence $x$. For a table $v \in R^n$ and a step $t$, the
forward step returns the table whose entry at a state $s$ is

$$\Bigl(\sum_{s'=0}^{n-1} v_{s'} \, \psi_t(s', s)\Bigr) \, \phi_{t+1}(s).$$
