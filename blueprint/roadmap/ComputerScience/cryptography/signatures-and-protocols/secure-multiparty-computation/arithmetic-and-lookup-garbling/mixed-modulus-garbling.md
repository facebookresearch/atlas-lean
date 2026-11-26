# Mixed-modulus circuits and BMR16 garbling

A *mixed-modulus circuit* has wires each carrying a residue modulo its own modulus $p$; addition and multiplication by constants act within one modulus, and *projection gates* apply an arbitrary function $\mathbb{Z}_p \to \mathbb{Z}_{p'}$. In the garbling of Ball, Malkin and Rosulek, every modulus $p$ has a global offset $\Delta_p \in \mathbb{Z}_p^\ell$, wire labels are $W_i + x_i\Delta_p$ (generalized Free-XOR), linear gates are free, and a projection gate with input modulus $p$ is garbled with $p - 1$ ciphertexts using a tweakable hash and a point-and-permute colour in $\mathbb{Z}_p$. *Mixed-modulus circular correlation robustness* asks that the oracle $(x, t, c) \mapsto H(x + c\Delta_p, t)$ be indistinguishable from random for nonzero $c$.

## Depends on

- [Affine wire labels for arithmetic garbling](affine-wire-labels.md)
- [Circular correlation robust hash functions](../garbling-scheme-security/circular-correlation-robustness.md)
- [Free-XOR garbling](../boolean-garbling-constructions/free-xor-garbling.md)

## Sources

- Marshall Ball, Tal Malkin and Mike Rosulek, "Garbling Gadgets for Boolean and Arithmetic Circuits", Proceedings of the 2016 ACM SIGSAC Conference on Computer and Communications Security, 2016.
