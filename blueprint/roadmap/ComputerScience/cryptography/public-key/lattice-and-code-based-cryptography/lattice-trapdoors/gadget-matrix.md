# The binary gadget vector and gadget matrix

Let $q = 2^w$. The *gadget vector* is $g = (1, 2, 4, \dots, 2^{w-1}) \in \mathbb{Z}_q^w$ and, for an index set of size $\ell$, the *gadget matrix* is the block-diagonal matrix

$$
G = I_\ell \otimes g^{\mathsf T} \in \mathbb{Z}_q^{\ell \times \ell w}.
$$

The *bit decomposition* $G^{-1}(u) \in \{0,1\}^{\ell w}$ of $u \in \mathbb{Z}_q^\ell$ lists the $w$ binary digits of every coordinate of $u$ (least significant first), so that $G\, G^{-1}(u) = u$; applied columnwise it decomposes matrices, $G\,G^{-1}(U) = U$. Dually, $s^{\mathsf T} G = (s_i 2^j)_{i,j}$ lists the powers-of-two multiples of each coordinate. These two maps are the "bit decomposition" and "powers of two" operations of GSW encryption.

## Sources

- Daniele Micciancio and Chris Peikert, "Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
