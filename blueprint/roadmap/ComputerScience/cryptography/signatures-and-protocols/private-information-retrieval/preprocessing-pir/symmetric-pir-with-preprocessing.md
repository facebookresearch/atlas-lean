# Symmetric PIR with client preprocessing: online transcripts

In *symmetric* PIR the client must additionally learn nothing about database entries other than those it queries. Consider single-server SPIR with client preprocessing for batches of $k$ queries on databases of $n \ge 2$ entries, in which the server's view of the online phase is the online transcript: (i) if the scheme is perfectly private against the server, the distribution of the online transcript is the same for every queried batch; (ii) the natural toy construction that uploads a random permutation applied to the query indices is not perfectly private over all batches when $k, n \ge 2$, since the upload reveals whether the batch contains repeated indices.

## Proof sketch

(i) Privacy for all batches equates the laws of the server's view, and the transcript is that view. (ii) A batch with a repeated index maps to a tuple with a repeated entry under any permutation.

## Depends on

- [Client-preprocessing single-server PIR](client-preprocessing-pir.md)

## Sources

- Alexander Hoover, Giuseppe Persiano and Kevin Yeo, "Lower Bounds for PIR with Preprocessing from Blackbox Cryptography", IEEE Symposium on Foundations of Computer Science (FOCS 2026), 2026.
