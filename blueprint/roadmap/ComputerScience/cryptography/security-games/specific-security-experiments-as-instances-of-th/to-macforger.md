# MAC forger with uniform coins from a coin-indexed forger

Let $R$ be finite and nonempty. A forger $A \colon R \to \mathrm{OracleComp}(M, T, M \times T)$, given as a map from coins to an oracle computation with tagging queries $M \to T$ that outputs a message and a tag, becomes a Framework MAC forger whose coins are uniform on $R$ and whose program on coins $r$ is $A(r)$.
