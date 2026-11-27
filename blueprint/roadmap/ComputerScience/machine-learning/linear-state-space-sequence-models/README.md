# Linear state-space sequence models

Linear algebra of recent state-space sequence layers such as Mamba and Mamba-2: for fixed parameters, a linear time-varying state-space recurrence acts along the sequence as multiplication by a semiseparable matrix, and a time-invariant one as a lower-triangular Toeplitz matrix, that is, a causal convolution. These pages are expositions of published results; each names the linear algebra it relies on, and how, under Informally uses. Semiseparable matrices are under [special matrices](../../../LinearAlgebra/special-matrices/semiseparable-matrices/README.md).

- [A state-space layer with fixed parameters is a semiseparable matrix](ssm-matrix-form.md)
- [Time-invariant state-space layers are lower-triangular Toeplitz matrices](lti-ssm-eq-lower-toeplitz.md)
- [Satisfiability of state space models is undecidable](satisfiability-of-state-space-models-undecidable.md)
