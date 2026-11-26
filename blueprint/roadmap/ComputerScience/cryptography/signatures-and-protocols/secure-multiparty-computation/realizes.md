# One-exchange realization

A protocol $\pi$ realizes a central bit functionality $B$ if and only if $\pi$ qualitatively
emulates $I_B$, the ideal protocol for $B$. In $I_B$ the main party forwards the environment's
API input bit to $B$ and returns the box's API reply bit to the environment. The simulator
supplies the box's backdoor input bit and receives its backdoor reply bit directly. On the
input and output pairs these wires are identity tables, one on each side of $B$.

## Sources

- one-exchange specialization of R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC Summer School (2025), slides 26–27.
