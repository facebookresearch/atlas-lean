# Algebraic properties of Micciancio–Peikert trapdoors

Let $A = [\,\bar A \mid HG - \bar A R\,]$ over $\mathbb{Z}_{2^w}$ with $H$ invertible. Then: (i) $R$ is a $G$-trapdoor for $A$ with tag $H$, and subtracting $(H - H')G$ from the right block yields the matrix with tag $H'$ and the same trapdoor; (ii) for every $z \in \Lambda^\perp_q(G)$ the lifted vector $\binom{Rz}{z}$ lies in $\Lambda^\perp_q(A)$ for every tag (since $Gz \equiv 0$), and in general $A \binom{Rz}{z} \equiv H G z$, so a preimage $z$ of $H^{-1}u$ under $G$ lifts to a preimage of $u$ under $A$; (iii) the columns of $\binom{R}{I} S$ (with $S = I \otimes S_w$) are in $\Lambda^\perp_q(A)$ for every tag, and if every entry in a row of $R$ has absolute value at most $B$ then the corresponding entries of $RS$ are at most $2 \ell w B$ in absolute value. Every SIS solution for $A$ is a vector of $\Lambda_q^\perp(A)$.

## Proof sketch

All claims follow by block matrix multiplication from $A \binom{R}{I} = HG$ and $GS \equiv 0$.

## Depends on

- [Micciancio–Peikert $G$-trapdoors and tagged parity-check matrices](micciancio-peikert-trapdoor.md)

## Proof depends on

- [The gadget lattice has a short basis-like matrix $S_w$](gadget-kernel-short-matrix.md)

## Sources

- Daniele Micciancio and Chris Peikert, "Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller", Advances in Cryptology – EUROCRYPT 2012, 2012.
