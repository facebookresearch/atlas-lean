# Proximity gap for Reed-Solomon codes on affine spaces (unique-decoding regime)

Let $\mathbb{F}$ be a finite field, $\mathrm{RS}_k \subseteq \mathbb{F}^n$ a Reed-Solomon code at distinct points with $2e + k \le n$, and $u_0, u_1, \dots, u_\ell \in \mathbb{F}^n$. Then either every point $u_0 + \sum_j z_j u_j$, $z \in \mathbb{F}^\ell$, is within Hamming distance $e$ of $\mathrm{RS}_k$, or the set $T$ of parameters whose point is $e$-close satisfies

$$|\mathbb{F}|\cdot|T| \le n\, |\mathbb{F}|^\ell,$$

that is, $T$ has density at most $n/|\mathbb{F}|$, uniformly in the dimension $\ell$.

## Proof sketch

If the density exceeds $n/|\mathbb{F}|$, correlated agreement on the affine space gives codewords $v_j$ agreeing with all $u_j$ on a common set of size at least $n - e$; then every point $u_0 + \sum_j z_j u_j$ agrees with the codeword $v_0 + \sum_j z_j v_j$ there and is $e$-close.

## Depends on

- [Correlated agreement of a tuple of words with a code](correlated-agreement.md)
- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Proof depends on

- [Correlated agreement for Reed-Solomon codes on affine spaces (unique-decoding regime)](reed-solomon-correlated-agreement-on-affine-spaces-unique-decoding.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
