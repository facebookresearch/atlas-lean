# Bisulfite-aware de Bruijn hash with Hamming control

**Definitions.** Let $\Sigma$ be a finite alphabet and $w \le m$. A function $h : \Sigma^m \to \{0,1\}^w$ is a de Bruijn hash function if for all $P,Q \in \Sigma^m$,

$$P[1..m-1] = Q[0..m-2] \ \Longrightarrow\ h(P)[1..w-1] = h(Q)[0..w-2],$$

i.e. $h$ maps edges of the order-$m$ de Bruijn graph to edges of the order-$w$ de Bruijn graph. For a text $T \in \Sigma^n$ with $n \ge m$, its hash $h(T) \in \{0,1\}^{n-m+w}$ is the unique string with $h(T)[i..i+w-1] = h(T[i..i+m-1])$ for $0 \le i \le n-m$ (well defined because consecutive fingerprints overlap consistently). A hash $h$ is Hamming-aware if there is a function $\phi$ such that every pattern within Hamming distance $k$ of $P$ has its fingerprint within the set $\{h(P) \oplus z : z \in Z(\phi(k))\}$ of small Hamming radius around $h(P)$.

**Lemma (pattern matching through hashes).** If $h$ is a de Bruijn hash function and $P \in \Sigma^m$ occurs in $T$ at position $i$, then $h(P)$ occurs in $h(T)$ at position $i$. The converse can fail (false positives), so candidate positions found in $h(T)$ must be verified against $T$.

**Bisulfite-aware hash.** Encode $\alpha(C) = \alpha(T) = 0$ and $\alpha(G) = \alpha(A) = 1$, extended to strings as binary numbers, and for $P \in \{A,C,G,T\}^m$ set

$$h^{\oplus}_{BS}(P) = \bigoplus_{i=0}^{\lceil m/w\rceil - 2} \alpha\big(P[iw..iw+w-1]\big)\ \oplus\ \alpha\big(P[m-w..m-1]\big),$$

the XOR of the encodings of consecutive length-$w$ blocks, the last block aligned to the end of $P$.

**Proposition.** $h^{\oplus}_{BS}$ is a de Bruijn hash function, it is invariant under C-to-T and G-to-A substitutions (so one index serves both converted strands), and it is Hamming-aware with

$$d_H(P_1,P_2) \le k \ \Longrightarrow\ d_H\big(h^{\oplus}_{BS}(P_1),\,h^{\oplus}_{BS}(P_2)\big) \le 2k.$$

Hence an approximate search for $P$ with up to $k$ mismatches only needs to visit fingerprints in the radius-$2k$ Hamming ball around $h^{\oplus}_{BS}(P)$, followed by verification.

## Expansion

The lemma is immediate from the definition of $h(T)$: the window of $h(T)$ starting at $i$ is by construction the fingerprint of the $m$-mer of $T$ starting at $i$. For the bisulfite hash, invariance holds because the encoding identifies C with T and G with A. A single substitution changes at most one bit in the encoding of each block that contains the position; since the final block may overlap the previous one, a position lies in at most two blocks, so each mismatch flips at most two bits of the XOR and $k$ mismatches flip at most $2k$. Indexing $h(T)$ with a succinct full-text index gives memory comparable to FM-index aligners while searching a much smaller neighbourhood than backtracking over all mismatch patterns.

## Sources

- N. Prezza, F. Vezzi, M. Käller, A. Policriti, "Fast, accurate, and lightweight analysis of BS-treated reads with ERNE 2", BMC Bioinformatics (2016), Definitions 1–4, Lemma 1 and Eq (1), <https://doi.org/10.1186/s12859-016-0910-3>, PMCID PMC4896272.
