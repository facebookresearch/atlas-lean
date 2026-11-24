# Is Neumann Unstable

The homogeneous steady state is *linearly unstable on `[0, L]`* (Neumann boundary
conditions): the finite-domain linearization has an eigenvalue with positive real part. This is
meaningful only for `0 < L`: at `L = 0` it holds exactly when the mode `k = 0`, i.e. `J` itself,
is unstable (see `IsNeumannEigenvalue`), although there is no domain.
