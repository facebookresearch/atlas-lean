# Bounds on RAF existence in elementary random catalysis networks

**Setting (Jain–Krishna or elementary model).** There are $N$ molecule types $S = \{v_1,\dots,v_N\}$, each produced by one reaction directly from food molecules, and each molecule type independently catalyzes the production of each molecule type (itself included) with probability $p$; food molecules catalyze nothing. Let $\mu = Np$, the expected number of molecule types whose formation a given molecule catalyzes, and let $P$ be the probability that some nonempty $S' \subseteq S$ has every element produced by a reaction catalyzed by an element of $S'$ (equivalently, that the network contains a RAF set).

**Theorem.** For every $\mu \in (0,1)$,

$$1 - e^{-\mu} \le P \le -\ln(1-\mu).$$

Consequently, for $P \ge 1/2$ the minimal required diversity satisfies

$$\frac{1 - e^{-1/2}}{p} \le N \le \frac{\ln 2}{p}.$$

**Comparison with the binary polymer model.** In the binary polymer model with polymers up to length $n$ (about $2^{n+1}$ molecule types and many more reactions than molecules), RAFs appear with high probability once $p(n-2)2^{n+1} = Cn$ for a constant $C$, so the required length is $n = \log_2 C - \log_2 p - 1 + o(1)$; the Erdős–Rényi giant-component heuristic underestimates this only by $\log_2(n-2) + O(1)$.

## Expansion

Lower bound: $P$ is at least the probability that some molecule catalyzes its own formation, $1-(1-p)^N \ge 1 - e^{-Np}$. Upper bound: a RAF exists iff the catalysis digraph (arc $v_i \to v_j$ when $v_i$ catalyzes the formation of $v_j$) has a directed cycle, because the food-generated condition is automatic. The expected number of directed $k$-cycles is $\binom{N}{k}(k-1)!\,p^k = N(N-1)\cdots(N-k+1)p^k/k \le \mu^k/k$, and by Markov's inequality $P \le \sum_{k\ge 1}\mu^k/k = -\ln(1-\mu)$. The resulting RAFs are tiny (a few molecule types, consistent with a power-law distribution of the length of the first cycle), whereas in the binary polymer model the ratio of reactions to molecules grows with $n$, so far fewer molecule types are needed but the RAFs that form are large.

## Sources

- Hordijk W, Steel M, Kauffman SA, "Molecular Diversity Required for the Formation of Autocatalytic Sets", Life (Basel) (2019), Section 3.1 (Eqs. (3)–(4)), Section 3.2, Theorem 1 and Eq. (5), <https://doi.org/10.3390/life9010023>, PMCID PMC6462942.
