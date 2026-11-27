# Affine wire labels for arithmetic garbling

In arithmetic garbling over a ring $R$, a wire carrying $x \in R$ is labelled by the *affine key encoding* $k + x\cdot s \in R^\ell$, where $k \in R^\ell$ is the wire key and $s \in R^\ell$ a global slope. Labels compose linearly for free: the sum of two labels under one slope is the label of the sum under the sum of keys, scaling a label by a public constant $c$ gives the label of $cx$ under the scaled key, and any public linear combination $\sum_i c_i (k_i + x_i s)$ is the label of $\sum c_i x_i$ under the key $\sum c_i k_i$.

## Sources

- Marshall Ball, Tal Malkin and Mike Rosulek, "Garbling Gadgets for Boolean and Arithmetic Circuits", Proceedings of the 2016 ACM SIGSAC Conference on Computer and Communications Security, 2016.
- Hanjun Li and Tianren Liu, "How to Garble Mixed Circuits that Combine Boolean and Arithmetic Computations", Advances in Cryptology – EUROCRYPT 2024, Part VI, 2024.
