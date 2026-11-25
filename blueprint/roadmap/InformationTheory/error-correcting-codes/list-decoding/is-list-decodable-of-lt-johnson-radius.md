# Every code is list decodable below the q-ary Johnson radius

Let $C$ be a code of length $n$ (a finite set of words in $\alpha^n$) over a finite alphabet $\alpha$ with $q = |\alpha| \ge 2$ letters, whose distinct codewords are at Hamming distance at least $d$. Let $J(q, \delta) = (1 - 1/q)\bigl(1 - \sqrt{\max(0,\, 1 - q\delta/(q-1))}\bigr)$ be the total $q$-ary Johnson radius, computed in $\mathbb{R}$ with $x/0 = 0$. If $e$ is a natural number with $e < J(q, d/n) \cdot n$ (with $d/n$ the real quotient, $0$ when $n = 0$), then $C$ is list decodable from $e$ errors with list size $q d n$: every Hamming ball of radius $e$ contains at most $q d n$ codewords.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 7.3.1.
- Guruswami and Sudan, "Extensions to the Johnson bound", 2001, Theorem 1.
