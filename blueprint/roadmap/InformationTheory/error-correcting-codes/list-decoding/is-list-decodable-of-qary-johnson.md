# List decodability from the integer Johnson conditions

Let $C$ be a code of length $n$ (a finite set of words in $\alpha^n$) over a finite alphabet $\alpha$ with $q = |\alpha| \ge 2$ letters, whose distinct codewords are at Hamming distance at least $d$. Let $e$ be a natural number with $q e \le (q-1) n$ and, in the integers,

$$(q-1)\,n\,(n-d) < (q-1)(n-e)^2 + e^2$$

Then $C$ is list decodable from $e$ errors with list size $q d n$: every Hamming ball of radius $e$ contains at most $q d n$ codewords: for every $y \in \alpha^n$, $|\{c \in C : \Delta(y, c) \le e\}| \le q d n$.
