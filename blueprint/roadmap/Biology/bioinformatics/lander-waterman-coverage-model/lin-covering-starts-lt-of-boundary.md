# Near-end bases of a linear genome have fewer than $L$ covering starts

On a linear genome with bases $\{0, \dots, G-1\}$ and reads of length $L \le G$ with start
positions $s \in \{0, \dots, G - L\}$, the read starting at $s$ covering $x$ when
$s \le x < s + L$: every base $x$ with $x + 1 < L$ or $G < x + L$ (fewer than $L - 1$ bases
before it, or fewer than $L - 1$ bases after it) is covered by fewer than $L$ starts.
