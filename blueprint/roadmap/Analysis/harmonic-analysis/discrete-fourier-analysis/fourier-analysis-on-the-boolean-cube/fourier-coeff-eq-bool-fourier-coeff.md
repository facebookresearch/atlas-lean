# Subset Fourier coefficients agree with cube Fourier coefficients

Let $E$ be a finite
subset of a type $\iota$ with $m$ elements, listed in a fixed order as $e_0, \dots, e_{m-1}$, and
decode a point $x$ of the Boolean cube of dimension $m$ as the subset
$D(x) = \{e_j : x_j = \mathrm{false}\}$ of $E$. Let $f$ be a function from finite subsets of
$\iota$ to $\mathbb{R}$ and let $S \subseteq E$. Then the Fourier coefficient
$\hat f(S) = 2^{-m} \sum_{U \subseteq E} f(U) (-1)^{|S \cap U|}$ of $f$ at $S$ over $E$ equals
the Fourier coefficient on the cube of the function $x \mapsto f(D(x))$ at the set of
coordinates $S' = \{j : e_j \in S\}$.
