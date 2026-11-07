# Correctness of the unimodal rearrangement algorithm

Let $a$ be an array of length $n$ that
is a permutation of $1, \dots, n$, and let $m(a)$ be the value that the program
$\mathrm{minRearrange}$ computes on $a$. Then some unimodal permutation $x$ of
$1, \dots, n$ differs from $a$ in exactly $m(a)$ positions, and every unimodal permutation of
$1, \dots, n$ differs from $a$ in at least $m(a)$ positions. So $m(a)$ is the minimum number of
positions in which $a$ differs from a unimodal permutation of $1, \dots, n$.

## Sources

- NWERC 2025 Problem G, see https://2025.nwerc.eu/problem-set.pdf Via leanprover/lean-eval@38361be, problem `permute_to_unimodal`.
