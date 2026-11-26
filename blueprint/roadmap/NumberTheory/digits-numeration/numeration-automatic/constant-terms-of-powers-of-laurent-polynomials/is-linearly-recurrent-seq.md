# Linearly recurrent sequence

A sequence $s = (s_n)_{n \in \mathbb{N}}$ with values in a
set $\alpha$ is linearly recurrent if there is $K \in \mathbb{N}$ such that for all
$i, i' \in \mathbb{N}$ and $\ell \ge 1$ with $s_{i'+t} = s_{i+t}$ for all $t < \ell$, there is $j$
with $0 < j \le K \ell$ and $s_{i'+j+t} = s_{i+t}$ for all $t < \ell$. That is, each occurrence
of a nonempty factor of length $\ell$ is followed by another occurrence starting at most
$K \ell$ positions later.

## Sources

- Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2, Definition 1.
