# Compression-collision reduction

Let $S$ have decidable equality. From a collision finder $A$ against the [keyed full Merkle–Damgård family](md-family.md) of a compression family $C$, the reduction is the collision finder against $C$ with

- the same coin distribution as $A$;
- on key $s$ and coins $r$: let $(M, M') = A(s, r)$; apply the block-level procedure $\mathrm{findCollision}$ for $h^s$, $\mathrm{iv}$ and $\ell$ to the [padded blocks](pad-blocks.md) of $M$ and of $M'$, at the same key and coins; return its pair $p$ on output $\mathrm{some}\ p$, and the pair $((\mathrm{iv}, \ell(0)), (\mathrm{iv}, \ell(0)))$ on output $\mathrm{none}$.

$\mathrm{findCollision}$ first compares the final compression inputs $(z_B, \ell(B))$ and $(z'_{B'}, \ell(B'))$ and returns them if they differ, without checking whether $h^s$ agrees on them; otherwise it walks back along both chains and returns the first differing pair of inputs, or $\mathrm{none}$. So the reduction does not test whether $p$ is a collision, and its fallback pair, two equal inputs, is never one.
