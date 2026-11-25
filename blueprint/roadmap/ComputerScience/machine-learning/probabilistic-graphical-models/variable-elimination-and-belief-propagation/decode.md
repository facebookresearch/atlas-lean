# Max-product decoding

An assignment of a tree model over a finite nonempty set of values,
defined by recursion on the number of vertices. For a single vertex, its value is one that
maximizes its unary factor. For vertices $0, \dots, n + 1$, the vertices $0, \dots, n$ get the
decoding of the model with the last vertex maximized out, and the last vertex gets a value $b$
maximizing $\psi(b, a)\, \phi(b)$, where $a$ is the decoded value of its parent, $\psi$ is the
factor of the edge between the last vertex and its parent and $\phi$ is the unary factor of the
last vertex; that is, $b$ attains the max-product message of the last vertex at $a$.
