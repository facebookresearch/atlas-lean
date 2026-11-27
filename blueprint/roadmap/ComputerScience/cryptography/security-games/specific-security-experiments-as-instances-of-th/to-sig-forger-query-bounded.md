# The embedded Lamport forger makes at most one query

Let $R$ be finite and nonempty. For every Lamport one-time forger $A$, every public key $pk$ and all coins $r$, the [embedded signature forger](to-sig-forger.md) on $pk$ and $r$ makes **at most** one signing query along every path. There is no hypothesis on $X$ or $Y$. This is a query bound used to place the forger in the one-time setting (Katz and Lindell, Section 12.6.1), not a security assertion; that the embedding makes exactly one query is a property of its definition, not the content of this bound.
