# List-decodable code

A code $C \subseteq \alpha^n$ is *list decodable from $e$ errors with list size $L$* if every
Hamming ball of radius $e$ contains at most $L$ codewords: for every received word
$y \in \alpha^n$,

$$|\{c \in C : \Delta(y, c) \le e\}| \le L.$$

Guruswami, Rudra and Sudan (Definition 7.2.1) call such a code $(\rho, L)$-list decodable, with
the radius written $\rho n$ for a fraction $\rho$ of errors; here the radius is the integer $e$.
For $L = 1$ and $e = \lfloor (d-1)/2 \rfloor$ this is unique decoding up to half the minimum
distance $d$.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definition 7.2.1.
