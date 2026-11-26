# Branch voltage drop

For natural numbers $n_N$ and $n_E$, a real $n_N \times n_E$ matrix $B$, complex node voltages
$V \in \mathbb{C}^{n_N}$ and a branch $e$, the voltage drop on $e$ is

$$d_e = \sum_{v} B_{ve} V_v,$$

the $e$-th entry of $B^{\mathsf T} V$, each real entry of $B$ read as a complex number. In the model
$B$ is the signed incidence matrix of the network, with entries $+1$ and $-1$ at the two ends of
each branch and $0$ elsewhere, so $d_e$ is the voltage at the end with entry $+1$ minus the voltage
at the end with entry $-1$; the definition allows any real matrix.
