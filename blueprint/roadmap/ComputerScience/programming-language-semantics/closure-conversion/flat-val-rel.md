# Flat value relation

The flat value relation between source values and target values is
the least relation with the following property. Let $b$ be a raw term, $\rho$ a list of source
values of length $|\rho|$, $c = (c_0, \dots, c_{m-1})$ the list of variables captured by
$\lambda. b$, and $w_0, \dots, w_{m-1}$ target values, as many as there are captured variables. If,
for every $k < m$, $c_k < |\rho|$ and the entry of $\rho$ at index $c_k$ (counting from $0$) is
related to $w_k$, then the source closure of $b$ over $\rho$ is related to the target value
$(\mathsf{code}\,B, \mathrm{enc}(w_0, \dots, w_{m-1}))$, where $B$ is the flat closure conversion
of $b$ with the flat accessors for $c$, and $\mathrm{enc}$ encodes a list of target values as
nested pairs ending in $\mathsf{unit}$.
