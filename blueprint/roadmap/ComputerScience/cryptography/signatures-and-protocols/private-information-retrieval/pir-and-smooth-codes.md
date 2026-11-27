# PIR from smooth codes and smooth codes from PIR

(i) A perfectly smooth $q$-query decoder for a code $C : \{0,1\}^n \to \Gamma^N$ (each query uniformly distributed over the $N$ positions) gives a perfectly private $q$-server PIR scheme: servers store $C(x)$, the user sends server $k$ the position $Q_k(i, r)$, and reconstructs with the decoder; its communication is $q(\lceil \log_2 N\rceil + \lceil \log_2|\Gamma|\rceil)$ bits (Yekhanin, Lemma 6.2 and its proof). (ii) Conversely, every perfectly correct, perfectly private one-round $2$-server PIR scheme for $n$-bit databases with $t$-bit queries and $a$-bit answers yields a code $C : \{0,1\}^n \to (\{0,1\}^a)^m$ of length $m \le 6 \cdot 2^t$ with a $(2, 3, \frac12)$-smooth decoder: it makes two nonadaptive queries, reads each position with probability at most $3/m$, and recovers every database bit with probability $1$; $C$ is linear when the servers' answers are linear combinations of the database bits (Goldreich, Karloff, Schulman and Trevisan, Lemma 7.1, with security and recovery parameters $\delta = 0$ and $\varepsilon = \frac12$).

## Proof sketch

(i) Each server's query is a uniform position, independent of $i$. (ii) View the scheme as an encoding whose positions are server–query pairs, each holding the corresponding answer. By privacy, the probability $p_j$ that the user reads position $j$ does not depend on the index; replicate position $j$ $\lceil p_j\, 2 \cdot 2^t \rceil$ times (at least once) and let the decoder simulate the PIR user, reading a uniform copy of each position it needs. Each copy is then read with probability at most $1/(2 \cdot 2^t)$, and the length is at most $6 \cdot 2^t$.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)
- [Locally decodable codes and smooth decoders](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/locally-decodable-codes/locally-decodable-codes-and-smooth-decoders.md)

## Sources

- Sergey Yekhanin, "Locally Decodable Codes", Foundations and Trends in Theoretical Computer Science, 2012, Section 6.1.1, Lemma 6.2.
- Oded Goldreich, Howard Karloff, Leonard J. Schulman and Luca Trevisan, "Lower Bounds for Linear Locally Decodable Codes and Private Information Retrieval", Computational Complexity 15, 2006, Lemma 7.1.
