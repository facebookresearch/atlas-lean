# Privacy transfer and statistical privacy for PIR

(i) *Privacy transfer:* if for every index $i$ the queries a scheme $P'$ sends for $i$ have the same joint law as the queries a private (respectively $t$-private) scheme $P$ sends for $f(i)$, for some map $f$ of indices, then $P'$ is private (respectively $t$-private). (ii) *Statistical privacy:* a scheme is $\delta$-statistically private when every server's (coalition's) query laws for any two indices are within statistical distance $\delta$; equivalently, all of them are within $\delta$ of the query law for a fixed reference index (up to a factor $2$), perfect privacy is $0$-statistical privacy, and privacy bounds are monotone in $\delta$. (iii) A perfectly correct scheme recovers the queried bit with advantage $1/2$ over guessing, and bounded-error recovery with advantage $\varepsilon$ is the notion under which lower bounds for PIR and locally decodable codes are stated.

## Proof sketch

(i) Privacy is a property of the query laws only. (ii) Triangle inequality for statistical distance.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
- Oded Goldreich, Howard Karloff, Leonard J. Schulman and Luca Trevisan, "Lower Bounds for Linear Locally Decodable Codes and Private Information Retrieval", Computational Complexity, 2006.
