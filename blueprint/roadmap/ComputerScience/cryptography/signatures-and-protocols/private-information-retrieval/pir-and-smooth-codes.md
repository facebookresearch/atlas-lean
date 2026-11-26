# PIR from smooth codes and smooth codes from PIR

(i) A perfectly smooth $q$-query decoder for a code $C : \{0,1\}^n \to \Gamma^N$ gives a perfectly private $q$-server PIR scheme: servers store $C(x)$, the user sends server $k$ the position $Q_k(i, r)$, and reconstructs with the decoder; its communication is $q(\lceil \log_2 N\rceil + \lceil \log_2|\Gamma|\rceil)$ bits. (ii) Conversely, every perfectly correct, perfectly private one-round $k$-server PIR scheme with query set $Q$ and answer set $A$ yields a code over $A$ whose positions are server–query pairs $(s, q)$, each replicated $\max(1, \lceil p_0(s, q)\,k|Q|\rceil)$ times where $p_0(s, q)$ is the probability that server $s$ receives $q$ for a fixed reference index; the code has length at most $(k + 1)\,k\,|Q|$ (at most $6|Q|$ for $k = 2$), is linear in the database when the answers are, and has a $k$-query decoder that is $(k+1)$-smooth (each position is read with probability at most $(k+1)/N'$, where $N' \le (k+1)\,k\,|Q|$ is the code length), so the code is locally decodable.

## Proof sketch

(i) Each server's query is a uniform position, independent of $i$. (ii) Replication proportional to the query probabilities makes the decoder that simulates the PIR user read each replica with probability at most $1/(k|Q|) \le (k+1)/N'$; privacy makes these probabilities independent of the index, so one replication works for all indices.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)
- [Locally decodable codes and smooth decoders](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/locally-decodable-codes/locally-decodable-codes-and-smooth-decoders.md)

## Sources

- Sergey Yekhanin, "Locally Decodable Codes", Foundations and Trends in Theoretical Computer Science, 2012.
- Oded Goldreich, Howard Karloff, Leonard J. Schulman and Luca Trevisan, "Lower Bounds for Linear Locally Decodable Codes and Private Information Retrieval", Computational Complexity, 2006.
