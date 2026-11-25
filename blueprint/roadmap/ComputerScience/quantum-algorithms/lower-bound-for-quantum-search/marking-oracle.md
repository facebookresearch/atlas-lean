# Phase oracle marking one item

Let $\iota$ (the query register) and $W$ (the workspace) be finite sets and consider the Hilbert space $\ell^2(\iota \times W)$ with basis states $|z, w\rangle$. For $y \in \iota$, the phase oracle marking $y$ is the linear isometry $O_y$ of $\ell^2(\iota \times W)$ given by

$$(O_y v)(z, w) = \begin{cases} -v(z, w) & \text{if } z = y, \\ v(z, w) & \text{otherwise,} \end{cases}$$

which negates the amplitude of every basis state whose query register holds $y$ and fixes the others (Bennett, Bernstein, Brassard and Vazirani, Section 3: inverting the phase of the marked item).
