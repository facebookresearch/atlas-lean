# Read covering a base of a circular genome

On a circular genome with positions $\{0, \dots, G-1\}$, a read of length $L$ starting at position $s$ covers the base $x$ if $(x - s) \bmod G < L$, that is, $x$ is one of $s, s+1, \dots, s + L - 1 \pmod G$.
