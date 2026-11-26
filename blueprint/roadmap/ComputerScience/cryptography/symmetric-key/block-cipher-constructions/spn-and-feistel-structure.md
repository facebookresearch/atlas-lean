# Structural properties of SPNs and Feistel networks

(i) A substitution–permutation network with bijective S-boxes, a bijective mixing layer and any key schedule (key mixing by XOR) is a permutation for every key, whatever the number of rounds. (ii) A Feistel round $(L, R) \mapsto (R, L + f(R))$ over any abelian group is a bijection for every round function $f$, and so is an unbalanced Feistel network. (iii) Periodicity: with the zero round function, Feistel rounds have period $2$; with the identity round function over a group of exponent two, they have period $3$. (iv) One Feistel round, and two Feistel rounds with independent random round functions, are distinguishable from a random permutation using one, respectively two, queries with advantage at least $1 - 1/(|G| - 1)$ when the halves range over a finite abelian group $G$ with $|G| \ge 3$, so three rounds are necessary for pseudorandomness.

## Proof sketch

(i) and (ii) compose bijections; the Feistel inverse is $(L', R') \mapsto (R' - f(L'), L')$. (iii) is a direct computation. (iv) One round leaks $R$ in the left output; for two rounds, queries $(L, R)$ and $(L', R)$ give left outputs differing by $L - L'$.

## Depends on

- [Luby–Rackoff theorem](../pseudorandom-constructions/lubyrackoff-theorem.md)

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
- Michael Luby and Charles Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing, 1988.
