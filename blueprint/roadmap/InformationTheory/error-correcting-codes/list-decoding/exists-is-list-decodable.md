# List-decodable codes of rate $1 - H_q(\rho) - 1/L$

Under the hypotheses of [list-decoding capacity, achievability](exists-encoding-list-decodable.md)
($q \ge 2$, $0 < \rho < 1 - 1/q$, $L \ge 1$, $k \le (1 - H_q(\rho) - 1/L) n$), there is a code
$C \subseteq \alpha^n$ that is [list decodable](is-list-decodable.md) from $\lfloor \rho n \rfloor$
errors with list size $L$ and has $q^k \le L \cdot |C|$. It is the set of codewords of the encoding
map: each codeword has at most $L$ preimages, since they all lie in the ball of radius $0$ around
it. Taking $k = \lfloor (1 - H_q(\rho) - 1/L) n \rfloor$, the rate of $C$ is at least
$1 - H_q(\rho) - 1/L - o(1)$, the set form of Theorem 7.4.2 (i) of Guruswami, Rudra and Sudan.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definition 7.2.1 and Theorem 7.4.2 (i).
