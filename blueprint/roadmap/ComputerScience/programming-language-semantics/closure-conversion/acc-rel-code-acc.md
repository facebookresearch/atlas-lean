# Code accessors implement the extended closure environment

Let $v$ be a source value
related to a target value $w$ by the value relation of closure conversion, and let $\rho$ and $ws$
be lists of source and target values of the same length such that, for every index $i$ below that
length, the entry of $\rho$ at $i$ is related to the entry of $ws$ at $i$. Then the code accessors
implement the source environment $v :: \rho$ ($\rho$ with $v$ added at index $0$) in the
one-element target environment whose entry is the pair of $w$ and the encoding of $ws$ as nested
pairs ending in $\mathsf{unit}$.
