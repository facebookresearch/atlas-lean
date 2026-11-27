# Alien k-mer rejection probability of an Othello index

**Othello.** Let $S$ be a set of $n$ k-mers, each with a category $T(s) \in V = \{1,\dots,v\}$, and let $C = \{0, 1, \dots, 2^l - 1\}$ with $l = \lceil \log_2(v+1)\rceil$. An Othello $O(S,V)$ consists of two uniform random hash functions $h_a, h_b$ and two arrays $A, B$ of $l$-bit integers of lengths $m_a = 2^{\lceil \log_2 n\rceil}$ and $m_b = 2^{\lceil \log_2 (4n/3)\rceil}$, so $2.67 n \le m_a + m_b < 4n$; it is built in $O(n)$ time, uses at most $4n\lceil\log_2(v+1)\rceil$ bits, and answers

$$\tau(s) = A[h_a(s)] \oplus B[h_b(s)]$$

with two memory accesses and one XOR. For $s \in S$, $\tau(s) = T(s)$. A k-mer $s' \notin S$ (an *alien*) is recognized as absent when $\tau(s') \in C \setminus V = \{0, v+1, \dots, 2^l - 1\}$ and is a false positive otherwise.

**Lemma 1.** Let $a_x$ and $b_x$ be the fractions of entries equal to $x$ in $A$ and $B$. For an alien $s'$,

$$p_x := \Pr[\tau(s') = x] = \sum_{t=0}^{2^l - 1} a_t\, b_{x \oplus t}.$$

**Lemma 2.** The probability $p_0$ that an alien is assigned category 0 satisfies $p_0 > 0.223$ as $n \to \infty$.

**Theorem.** For any alien k-mer $s' \notin S$,

$$P_{\text{Alien}} = p_0 + \sum_{x = v+1}^{2^l - 1} p_x,$$

and $P_{\text{Alien}} > 0.223$ as $|S| \to \infty$.

## Proof depends on

- [Cuckoo insertion succeeds without rehashing with high probability](../../../../ComputerScience/data-structures/hashing/cuckoo-hashing/cuckoo-insertion-succeeds-without-rehashing.md)

## Expansion

An alien hashes to independent uniform positions of $A$ and $B$, so $\tau(s') = x$ exactly when the two looked-up entries $t$ and $t \oplus x$ XOR to $x$, giving Lemma 1. Array entries never hit by a stored key stay $0$; a fixed position of $A$ is missed by all $n$ keys with probability $(1 - 1/m_a)^n \to e^{-n/m_a}$, and similarly for $B$. Hence $p_0 = \sum_x a_x b_x \ge a_0 b_0 \to e^{-n(1/m_a + 1/m_b)}$, and the power-of-two sizes give $1 < n(1/m_a + 1/m_b) \le 1.5$, so $p_0 \ge e^{-1.5} \approx 0.223$. The theorem sums $p_x$ over the unused categories.

## Sources

- Y. Yu, J. Liu, X. Liu, Y. Zhang, E. Magner, E. Lehnert, C. Qian, J. Liu, "SeqOthello: querying RNA-seq experiments at scale", Genome Biology 19 (2018) 167, Methods Section 1 (properties of Othello; Lemmas 1–2 and Theorem 1), <https://doi.org/10.1186/s13059-018-1535-9>, PMCID PMC6194578.
