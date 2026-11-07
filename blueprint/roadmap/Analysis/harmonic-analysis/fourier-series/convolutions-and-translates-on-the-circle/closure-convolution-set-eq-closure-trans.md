# Convolutions and linear combinations of translates have the same closure

Let
$T = \mathbb{R}/2\pi\mathbb{Z}$ with the measure induced by Lebesgue measure on $[0, 2\pi)$, and
let $L^1(T)$ be the space of real-valued integrable functions on $T$ modulo equality almost
everywhere. Fix a real-valued integrable $f$ on $T$. Let $B_f \subseteq L^1(T)$ be the set of
classes of the finite linear combinations of translates
$x \mapsto \sum_{i=1}^N a_i f(x - \tau_i)$ with $N \in \mathbb{N}$, $a_i \in \mathbb{R}$ and
$\tau_i \in T$, and let $M_f \subseteq L^1(T)$ be the set of classes of the convolutions
$(f * g)(x) = \int_T f(y)\, g(x - y)\,dy$ with $g$ real-valued and integrable on $T$. Then $M_f$
and $B_f$ have the same closure in $L^1(T)$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Commutative Banach algebras and commutative topological algebras), `benchmark/level2/ma_proofbench_l2_12.lean` at openbmb/ma-proofbench@31bab4c.
