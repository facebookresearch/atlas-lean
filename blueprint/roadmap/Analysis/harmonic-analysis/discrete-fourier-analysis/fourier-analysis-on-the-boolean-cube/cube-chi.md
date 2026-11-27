# Fourier character on the Boolean cube

For a set $S$ of coordinates among $n$, the Fourier
character $\chi_S$ is the real-valued function on the Boolean cube in $n$ coordinates given by
$\chi_S(x) = \prod_{i \in S} \sigma(x_i)$, where $\sigma$ is the sign of a coordinate:
$\sigma(\text{true}) = 1$ and $\sigma(\text{false}) = -1$.

Equivalently, for bitstrings $x, s \in \{0, 1\}^n$ the sign $(-1)^{x \cdot s} = \prod_i (-1)^{x_i s_i}$, read as a complex number, is $\chi_S$ for the support $S$ of $s$ evaluated at the point of the cube that is true exactly where $x$ has the bit $0$.
