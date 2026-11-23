# Fence tilings and strongly restricted permutations

Let $D$ be a finite set of integers
and $n$ a natural number. Number the cells of an $n$-board $0, 1, \dots, n-1$ and give cell $i$
a left slot $2i$ and a right slot $2i + 1$. A fence $(s, g)$, with $s$ and $g$ natural numbers,
has teeth in slots $s$ and $s + 1 + 2g$. A tiling is a finite set of fences such that every
fence $(s, g)$ in it satisfies $s + 1 + 2g < 2n$ and either $s$ is even and $g \in D$, or $s$ is
odd and $-g - 1 \in D$, and such that every slot $x < 2n$ is a tooth of exactly one of its
fences. A tiling $t$ and a permutation $\pi$ of $\{0, 1, \dots, n-1\}$ are compatible if for
every cell $i$ and every fence $(s, g) \in t$: if $s = 2i$ then $\pi(i) = i + g$, and if
$s + 1 + 2g = 2i$ then $\pi(i) = i - g - 1$. Then for every tiling $t$ there is exactly one
permutation $\pi$ with $\pi(i) - i \in D$ for all $i$ that is compatible with $t$, and for every
permutation $\pi$ with $\pi(i) - i \in D$ for all $i$ there is exactly one tiling compatible
with $\pi$.

The lemma is due to Edwards and Allen (2015); the fences are $(\tfrac12, g)$-fences.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Lemma 12.
