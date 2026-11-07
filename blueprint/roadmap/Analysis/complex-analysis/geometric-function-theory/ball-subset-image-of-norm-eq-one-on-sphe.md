# Nonconstant holomorphic functions of modulus one on the unit circle cover the unit disc

Let $U\subseteq\mathbb{C}$ be a connected open set containing the closed unit disc
$\{z:|z|\le 1\}$, and let $f:\mathbb{C}\to\mathbb{C}$ be holomorphic on $U$ and non-constant on
$U$. If $|f(z)|=1$ whenever $|z|=1$, then every $w$ with $|w|<1$ is $f(z)$ for some $z\in U$; that
is, $f(U)$ contains the open unit disc.

The connectedness of $U$ is added to the source statement, which asks only for an open set: for
$U=\{z:|z|<2\}\cup\{z:|z-10|<1\}$, with $f=1$ on the first disc and $f(z)=z$ on the second, $f$
is non-constant and holomorphic on $U$ and has modulus one on the unit circle, but $f(U)$ does not
contain the open unit disc.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex variable; General properties of functions of one complex variable), `benchmark/level1/ma_proofbench_l1_25.lean` at openbmb/ma-proofbench@31bab4c, with the change above.
