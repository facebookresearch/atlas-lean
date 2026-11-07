# Cubic lattice walks and colored Motzkin paths

Let $n$ and $k$ be natural numbers, and let
$e_0, \dots, e_n$ be the standard basis vectors of $\mathbb{Z}^{n+1}$. Count the walks of $k$
steps in the cubic lattice $\mathbb{Z}^{n+1}$ that start at the origin, in which each step is
$+e_i$ or $-e_i$ for some $i \in \{0, \dots, n\}$ and, counting only the steps in the last
coordinate $i = n$, every initial segment has at least as many $+e_n$ steps as $-e_n$ steps and
the whole walk has equally many. Their number equals the number of words of length $k$ in the
letters $U$, $D$ and $L_1, \dots, L_{2n}$ in which every initial segment has at least as many
letters $U$ as letters $D$ and the whole word has equally many, that is, the number of Motzkin
paths of length $k$ with one color of up step, one color of down step and $2n$ colors of level
step.

In the source's notation this is the theorem in dimension $n + 1$: only the last coordinate is
constrained, and the $2n$ steps $\pm e_i$ with $i < n$ correspond to the $2n$ level-step colors.

## Sources

- Rigoberto Flórez, Leandro Junes, and José L. Ramírez, "Further Results on Paths in an n-Dimensional Cubic Lattice," Journal of Integer Sequences 21 (2018), Article 18.1.2, Theorem (label bijection:Motzkin), lines 924–926, https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.tex
