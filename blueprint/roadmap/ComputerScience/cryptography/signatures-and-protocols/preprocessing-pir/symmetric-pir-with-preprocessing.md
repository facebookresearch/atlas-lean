# Symmetric PIR with client preprocessing: online transcripts and storage bounds

In *symmetric* PIR the client must additionally learn nothing about database entries other than those it queries. In a restricted model of single-server SPIR with client preprocessing for batches of $k$ queries on databases of $n \ge 2$ entries: (i) perfect privacy implies that the online transcript is independent of the queried batch; (ii) consequently any such scheme that is correct for every batch must store client state whose size is at least proportional to $\log_2$ of the number of batches it can serve, giving a lower bound on client storage of order $k \log n$ bits per supported query batch; (iii) the natural toy construction that uploads a random permutation applied to the query indices is not perfectly private over all batches when $k, n \ge 2$, since the upload reveals whether the batch contains repeated indices.

## Proof sketch

(i) Privacy for all batches equates the transcript laws. (ii) With an index-independent transcript, the client's answer is a function of its stored state and the transcript, so the state must encode every answer it can return. (iii) A batch with a repeated index maps to a tuple with a repeated entry under any permutation.

## Depends on

- [Client-preprocessing single-server PIR](client-preprocessing-pir.md)

## Sources

- Alexander Hoover, Giuseppe Persiano and Kevin Yeo, "Lower Bounds for PIR with Preprocessing from Blackbox Cryptography", IEEE Symposium on Foundations of Computer Science (FOCS 2026), 2026.
