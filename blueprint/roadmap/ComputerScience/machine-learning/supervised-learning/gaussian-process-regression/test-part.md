# Test-value projection

For finite index sets $\tau$ (test inputs) and $\nu$ (training
inputs), the test-value projection is the $\tau \times (\tau \sqcup \nu)$ real matrix with the
identity matrix on the columns indexed by $\tau$ and a zero block on the columns indexed by $\nu$.
It sends a joint vector $(u, y)$ with $u \in \mathbb{R}^{\tau}$ and $y \in \mathbb{R}^{\nu}$ to its
block of test values $u$.
