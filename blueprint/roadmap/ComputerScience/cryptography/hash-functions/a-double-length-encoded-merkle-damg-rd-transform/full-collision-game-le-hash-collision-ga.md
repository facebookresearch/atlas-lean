# Full-hash collisions are block-level collisions

Let the chaining values $S$ have decidable equality and the coins $R$ be finite and nonempty, with $0 < n$ and $\mathrm{maxLen} + L + n \le n \cdot \mathrm{maxBlocks}$. For every adversary $A : R \to \{0,1\}^* \times \{0,1\}^*$, with $r$ drawn **uniformly** from $R$ in both games,

$$
\Pr_r\bigl[A(r) = (M, M'),\ M \ne M',\ |M|, |M'| < \mathrm{maxLen},\ H(M) = H(M')\bigr]
\le
\Pr_r\bigl[A'(r) = (X, X'),\ X \ne X',\ |X|, |X'| < \mathrm{maxBlocks},\ H_{\mathrm{blk}}(X) = H_{\mathrm{blk}}(X')\bigr],
$$

where $H$ is the [full hash](full-hash.md), $H_{\mathrm{blk}}(x_1, \dots, x_B) = h(z_B, \ell(B))$ is the block-level Merkle–Damgård hash with the same $h$, $\mathrm{iv}$ and $\ell$, and $A'$ is the [block adversary](block-adversary.md), which outputs the [padded blocks](pad-blocks.md) of both messages of $A(r)$. No hypothesis on the length block is needed for this step.
