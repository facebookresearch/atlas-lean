# Correctness of the unimodal rearrangement algorithm

For an array $a = (a_0, \dots, a_{n-1})$ of natural numbers, let $m(a)$ be the following value.
Form the list of pairs consisting of $(2i + 1,\ 2(a_i - i - 1))$ for every index $i$ with
$i + 1 \le a_i$, followed by $(2(a_i + i - n),\ 2(n - i) - 1)$ for every index $i$ with
$n \le a_i + i$ (indices in increasing order, subtraction truncated at $0$); sort the pairs
lexicographically in nondecreasing order; let $L$ be the length of a longest nondecreasing
subsequence of the sequence of their second components ($L = 0$ if there are no pairs); and put
$m(a) = n - L$.

Let $a$ be an array of length $n$ that is a permutation of $1, \dots, n$. Then some unimodal
permutation $x$ of $1, \dots, n$ differs from $a$ in exactly $m(a)$ positions, and every unimodal
permutation of $1, \dots, n$ differs from $a$ in at least $m(a)$ positions. So $m(a)$ is the
minimum number of positions in which $a$ differs from a unimodal permutation of $1, \dots, n$.

## Sources

- NWERC 2025, Problem G (*Group Photo*), <https://2025.nwerc.eu/problem-set.pdf>. Problem `permute_to_unimodal` of the lean-eval benchmark.
