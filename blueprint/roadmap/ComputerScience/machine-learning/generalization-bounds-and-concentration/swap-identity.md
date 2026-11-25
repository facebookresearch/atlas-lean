# Dataset swap identity

Assume that `Z` is finite.

The swap identity behind uniform-stability generalization proofs.
Datasets are `S : Fin n → Z`; `A` maps a dataset to a hypothesis and `ℓ h z`
is the loss of `h` on sample `z`, with values in an additive commutative
monoid `R`. For each coordinate `i`, summing the loss of the algorithm trained
on the dataset with coordinate `i` replaced by a fresh sample, evaluated at
the replaced sample, over all datasets and fresh samples, equals summing the
loss of the algorithm trained on the original dataset at a fresh sample. The
bijection swaps the fresh sample with the `i`-th dataset entry.
