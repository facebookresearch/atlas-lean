# Soundness of the graph 3-coloring protocol

A *commitment scheme* is a polynomial-time machine $\mathrm{Com}$ with a polynomial $\ell$ such that commitments are perfectly binding, $\mathrm{Com}(v_0, r_0) \ne \mathrm{Com}(v_1, r_1)$
for all $v_0 \ne v_1$ in $\{0,1\}^n$ and all $r_0, r_1 \in \{0,1\}^{\ell(n)}$, and computationally hiding: for every non-uniform probabilistic polynomial-time distinguisher $D$ there is a
negligible $e$ such that $\bigl|\Pr[D(\mathrm{Com}(v_0, r)) = 1] - \Pr[D(\mathrm{Com}(v_1, r)) = 1]\bigr| \le e(n)$ for uniform $r$ and all $v_0, v_1 \in \{0,1\}^n$.

Consider the protocol for graph 3-coloring on $G = (V, E)$ with $|V| = n$ and $|E| \ge 1$. In each round the prover chooses a uniformly random permutation $\pi$
of the three colors and commits to the color $\pi(c_i)$ of every vertex $i$; the verifier picks a uniformly random edge $(i, j) \in E$; the prover opens the
commitments at $i$ and $j$; and the verifier accepts the round if the two opened colors are distinct elements of $\{1, 2, 3\}$. The rounds are repeated $n|E|$ times.

The honest prover holding a proper 3-coloring is always accepted. If $G$ is not 3-colorable, then by perfect binding each round fixes one committed value per vertex; replacing every value outside
$\{1, 2, 3\}$ by $1$ gives a 3-coloring with a monochromatic edge, and on that edge the opened colors are equal or one of them lies outside
$\{1, 2, 3\}$. So a cheating prover is caught in each round with probability at least $1/|E|$, and is accepted in all $n|E|$ rounds
with probability at most $(1 - 1/|E|)^{n|E|} \le e^{-n}$.

## Depends on

- [Zero-knowledge interactive proofs](zero-knowledge-interactive-proofs.md)

## Sources

- R. Pass and A. shelat, *A Course in Cryptography*, lecture notes, Cornell University, 2010, <https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf>: Definition 126.3 (commitment), Protocol 127.5 and the soundness part of the proof of Proposition 127.6.
