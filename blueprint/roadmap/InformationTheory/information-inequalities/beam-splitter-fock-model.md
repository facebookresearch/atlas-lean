# Bosonic Fock states and the passive beam-splitter output condition

On the Hilbert space $\ell^2(\mathbb N^n;\mathbb C)$, let $|k\rangle$ denote the number basis. A state is a bounded positive operator for which the real diagonal entries have sum one (including summability). Finite energy means summability of that diagonal weighted by $\sum_j k_j$. Entropy is the totalized real sum of the real diagonal entries of the continuous functional calculus for $z\mapsto-\operatorname{Re}z\log(\operatorname{Re}z)$; the function vanishes at zero.

For one mode, the coefficient from input occupation $(a,b)$ to output $(k,e)$ is the coefficient of $(c^\dagger)^k(d^\dagger)^e$ after substituting $a^\dagger=\sqrt{\eta}c^\dagger-\sqrt{1-\eta}d^\dagger$ and $b^\dagger=\sqrt{1-\eta}c^\dagger+\sqrt{\eta}d^\dagger$ into the input monomial, multiplied by $\sqrt{k!e!/(a!b!)}$. It is zero off $k+e=a+b$. In $n$ modes multiply the coefficients. For retained occupations $k,l$ and discarded occupation $e$, sum the resulting coefficient products against the entries of the product input over the two finite sets of number-conserving occupation splits. The output condition is that for every $k,l$ the series over all $e$ has sum equal to that entry of the output state. It uses actual summability in this condition, not only equality to a totalized sum.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EntropyPhotonNumber.lean#L12-L95)
