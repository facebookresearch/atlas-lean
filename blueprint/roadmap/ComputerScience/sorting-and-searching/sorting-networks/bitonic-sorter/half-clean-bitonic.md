# The half-cleaner lemma

Let $m \in \mathbb{N}$ and let $s_0, s_1, \dots, s_{2m-1}$ be a
bitonic sequence of Booleans, ordered by $\mathrm{false} < \mathrm{true}$. For $i < m$ put
$\ell_i = \min(s_i, s_{i+m})$ and $u_i = \max(s_i, s_{i+m})$. Then either $\ell_i = \mathrm{false}$
for every $i < m$ and $u_0, \dots, u_{m-1}$ is bitonic, or $u_i = \mathrm{true}$ for every
$i < m$ and $\ell_0, \dots, \ell_{m-1}$ is bitonic.

The $\ell_i$ and $u_i$ are the outputs of the half-cleaner on $2m$ wires. This is CLRS Lemma 27.3
for bitonic $0$-$1$ sequences.
