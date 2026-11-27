# The tabulated forward algorithm for chain CRFs

For a chain conditional random field with
states $0, \dots, n - 1$ and weights in a semiring, and an observation stream $x$, the tabulated
partition function at time $t$ is the sum of the entries of the forward table at time $t$, the
vector $(\alpha_t(0), \dots, \alpha_t(n - 1))$ of forward variables computed step by step from
time $0$.

It equals the partition function at time $t$ and takes $O(t n^2)$ operations.
