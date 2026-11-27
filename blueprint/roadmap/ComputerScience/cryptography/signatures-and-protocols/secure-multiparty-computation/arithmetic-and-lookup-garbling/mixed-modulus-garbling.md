# Mixed-modulus circuits and BMR16 garbling

A *mixed-modulus circuit* (a mixed-modulus simple circuit of Ball, Malkin and Rosulek) has wires each carrying a residue modulo its own modulus $m$; its internal gates are addition modulo $m$ (of unbounded fan-in, all wires mod $m$), multiplication by a public constant $c$ that is a unit modulo $m$ (input and output wires mod $m$), and *projection gates* applying an arbitrary function $\varphi : \mathbb{Z}_m \to \mathbb{Z}_n$ from a mod-$m$ wire to a mod-$n$ wire. In their garbling, every modulus $m$ has a global offset $\Delta_m$, a uniform vector over $\mathbb{Z}_m$ whose last (colour) digit is $1$; wire labels are $W_i^0 + x\Delta_m$ (generalized Free-XOR), so addition and multiplication by units are free; and a projection gate $g$ with input wire $i$ (modulus $m$) and output wire $j$ (modulus $n$) is garbled with $m - 1$ ciphertexts (after row reduction) of the form $H(g, W_i^0 + x\Delta_m) + W_j^0 + \varphi(x)\Delta_n$, indexed by the colour digit of the input label, using a hash $H$ with the gate index $g$ as tweak. *Mixed-modulus circular correlation robustness* asks that, with the offsets $\Delta_{m_1}, \dots, \Delta_{m_r}$ uniform, the oracle

$$
O(g, i, j, X, a, c) = H(g, X + a\Delta_{m_i}) + c\Delta_{m_j}
$$

(inner addition modulo $m_i$, outer addition modulo $m_j$) be indistinguishable from a random function for every polynomial-time adversary that queries it on distinct values of $g$ and with $a \ne 0$.

## Depends on

- [Affine wire labels for arithmetic garbling](affine-wire-labels.md)
- [Circular correlation robust hash functions](../garbling-scheme-security/circular-correlation-robustness.md)
- [Free-XOR garbling](../boolean-garbling-constructions/free-xor-garbling.md)

## Sources

- Marshall Ball, Tal Malkin and Mike Rosulek, "Garbling Gadgets for Boolean and Arithmetic Circuits", Proceedings of the 2016 ACM SIGSAC Conference on Computer and Communications Security, 2016.
