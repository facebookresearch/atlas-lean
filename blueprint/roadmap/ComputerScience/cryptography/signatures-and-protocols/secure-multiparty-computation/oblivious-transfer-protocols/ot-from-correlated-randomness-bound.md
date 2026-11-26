# Information-theoretic upper bound on oblivious transfer from correlated randomness

Let Alice and Bob hold samples $(A, B)$ of a correlated source and run any two-party protocol with a public transcript $T$ (plain channels, private coins), at the end of which they hold $k$ bits of random oblivious transfer: Alice has $(S_0^j, S_1^j)_{j<k}$, Bob has a choice vector $C$ and $S^j_{C_j}$, with perfect correctness and perfect semi-honest security. Then

$$
k \le I(A; B),
$$

the mutual information of the source. In particular, the $(2, 1; 1)$ card deal source, in which Alice receives two and Bob one of four distinct cards uniformly, has $I(A;B) = 1$ bit and yields at most one random OT bit.

## Proof sketch

Security against each party forces conditional independence relations between the outputs and the other party's view given the transcript; combined with the chain rule and the fact that a public transcript cannot increase $I(A;B \mid T)$ beyond $I(A;B)$, each ROT bit consumes one bit of conditional mutual information.

## Depends on

- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](oblivious-transfer-functionalities.md)

## Sources

- Rudolf Ahlswede and Imre Csiszár, "On Oblivious Transfer Capacity", 2007 IEEE International Symposium on Information Theory, 2007.
- Rudolf Ahlswede and Imre Csiszár, "Common Randomness in Information Theory and Cryptography. Part I: Secret Sharing", IEEE Transactions on Information Theory, 1993.
