# Block-recursive millionaires' comparison from oblivious transfer

CrypTFlow2's millionaires' protocol gives two parties XOR shares of $\mathbf 1\{x<y\}$ for $\ell$-bit inputs $x$ (party 0) and $y$ (party 1). It splits both into blocks of at most $m$ bits, gets shares of each block's less-than and equality bits by oblivious transfer, and combines them up a tree by $\mathbf 1\{x<y\}=\mathbf 1\{x_1<y_1\}\oplus(\mathbf 1\{x_1=y_1\}\wedge\mathbf 1\{x_0<y_0\})$.

For unsigned integers $x=x_1\|x_0$, $y=y_1\|y_0$ (high part first) the displayed identity and $\mathbf 1\{x=y\}=\mathbf 1\{x_1=y_1\}\wedge\mathbf 1\{x_0=y_0\}$ hold. Let $\ell,m\ge1$, $q=\lceil\ell/m\rceil$, and split $x=x_{q-1}\|\dots\|x_0$, $y=y_{q-1}\|\dots\|y_0$ into blocks of $m$ bits except the high block, of $\ell-(q-1)m$ bits.

- *Leaves.* For each $j<q$, with $M_j=2^{(\text{width of block }j)}$, party 0 samples fresh uniform bits $\langle\mathrm{lt}_{0,j}\rangle_0,\langle\mathrm{eq}_{0,j}\rangle_0$ and for $k<M_j$ sets $s_{j,k}=\langle\mathrm{lt}_{0,j}\rangle_0\oplus\mathbf 1\{x_j<k\}$, $t_{j,k}=\langle\mathrm{eq}_{0,j}\rangle_0\oplus\mathbf 1\{x_j=k\}$; by $\binom{M_j}{1}$-OT with receiver choice $y_j$, party 1 learns $s_{j,y_j}$ and $t_{j,y_j}$, its shares of $\mathbf 1\{x_j<y_j\}$ and $\mathbf 1\{x_j=y_j\}$.
- *Internal nodes.* Children are combined by $\mathrm{lt}=\mathrm{lt}_{\mathrm{hi}}\oplus(\mathrm{eq}_{\mathrm{hi}}\wedge\mathrm{lt}_{\mathrm{lo}})$ and $\mathrm{eq}=\mathrm{eq}_{\mathrm{hi}}\wedge\mathrm{eq}_{\mathrm{lo}}$, with XOR local and AND by a functionality returning fresh XOR shares of the product; when $q$ is a power of two this is a perfect binary tree of depth $\log q$, and otherwise maximal perfect subtrees are combined by the same rule.
- *Output.* The parties' shares of the root's $\mathrm{lt}$.

Correctness, by induction from the leaves: the root shares XOR to $\mathbf 1\{x<y\}$.

## Depends on

- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](../../signatures-and-protocols/secure-multiparty-computation/oblivious-transfer-protocols/oblivious-transfer-functionalities.md)
- [Shared multiplication from 1-out-of-4 oblivious transfer](../../signatures-and-protocols/secure-multiparty-computation/semi-honest-mpc-foundations/ot14-shared-multiplication.md)

## Proof depends on

None.

## Expansion

Not ready: the leaves use 1-out-of-$2^w$ oblivious transfer for block widths $w$, while main defines only 1-out-of-2, batched and 1-out-of-4 transfer. The AND steps use the shared-multiplication functionality's interface (uniform XOR shares of the product), not a particular implementation. The source's semi-honest security claim in the ideal-OT and ideal-AND hybrid is a separate statement.

## Sources

- Deevashwer Rathee, Mayank Rathee, Nishant Kumar, Nishanth Chandran, Divya Gupta, Aseem Rastogi, Rahul Sharma, "CrypTFlow2: Practical 2-Party Secure Inference", ACM CCS 2020, DOI 10.1145/3372297.3417274; numbers and equations from the author-deposited arXiv:2010.06457v1: rendered p. 5, §3.1, Equation (1) and Algorithm 1.
