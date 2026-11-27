# Up-front and fresh randomness give the same CPA experiment

Let the key space $K$, the randomness space $X$ and the adversary's coin space $R$ be finite and nonempty, and let $Y$ be an additive commutative group. Let $F \colon K \to X \to Y$ and let $A$ be a coin-indexed CPA adversary such that its [uniform-coin embedding](to-cpaadversary.md) makes at most $q$ encryption queries in total along every path. Then the PRF file's CPA game with tape length $q$ equals the Framework CPA game $\mathrm{PrivK}^{\mathrm{cpa}}$ of the [PRF-based scheme](prf-enc.md) against the embedded adversary, which draws fresh encryption randomness for each query (Katz and Lindell, Construction 3.30 and Definition 3.22).

The PRF file's game draws a key $k$, a tape $\rho \in X^q$, challenge randomness $r_s \in X$, a bit $b$ and coins $r$ uniformly and independently, and outputs whether the fixed-tape guess equals $b$; in that guess the two stages share the entries of $\rho$, the challenge is $(r_s, F(k, r_s) + m_b)$, and a query beyond the $q$ tape entries makes the guess `false`.

The query bound is a sufficient condition. Without it the equality is not guaranteed, since the two experiments behave differently on an adversary that overflows the tape; it can still hold, for example for $q = 0$ and an adversary that makes one query and always guesses `false`.
