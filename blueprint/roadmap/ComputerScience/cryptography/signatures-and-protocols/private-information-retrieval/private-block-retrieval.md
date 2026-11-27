# Private block retrieval

Let $\mathrm{PIR}_k(n, \ell)$ denote retrieving one of $n$ blocks of $\ell$ bits replicated on $k$ servers, by a one-round scheme. (i) If $\mathrm{PIR}_k(n, 1)$ has a scheme in which the user sends $\alpha_k(n)$ bits to each server and receives $\beta_k(n)$ bits from each, then $\mathrm{PIR}_k(n, \ell)$ has one with $\alpha_k(n)$ query bits and $\ell\,\beta_k(n)$ answer bits per server: run the bit scheme on each of the $\ell$ bit-slices with the same queries. (ii) If moreover each server answers with a single bit and the user reconstructs the desired bit as the sum modulo $2$ of the $k$ answer bits, then for every $m > 1$, $\mathrm{PIR}_k(m(n-1), 1)$ has a scheme with $m\,\alpha_k(n)$ query bits and one answer bit per server: split the database into $m$ strings of $n - 1$ bits, each padded with a dummy zero bit at position $n$; to retrieve bit $i_2$ of string $i_1$, the user runs the bit scheme $m$ times in parallel, asking in the $j$-th instance for position $i_2$ if $j = i_1$ and for the dummy position $n$ otherwise, and each server sends the sum modulo $2$ of its $m$ answers. (iii) Combining both, for such bit schemes and all $\ell, m > 1$, $\mathrm{PIR}_k(m(n-1), \ell)$ has a scheme with $m\,\alpha_k(n)$ query bits and $\ell$ answer bits per server; in particular, when $\ell$ divides $n$, $\mathrm{PIR}_k(n, \ell)$ costs $\ell$ times the communication of $\mathrm{PIR}_k(n/\ell + 1, 1)$. These transformations preserve perfect correctness and $t$-privacy. In particular, the single-server (or full-coalition) block retrieval needs exactly $n\ell$ bits, attained by downloading.

## Proof sketch

Privacy of the transformations reduces to that of the bit scheme, since each server receives independent queries of the bit scheme. Correctness of (ii): the answers of instance $j$ sum to the requested bit for $j = i_1$ and to the dummy bit $0$ otherwise, so exchanging the two sums modulo $2$ shows that the servers' single bits sum to the requested bit.

## Depends on

- [Private information retrieval schemes](pir-schemes.md)

## Proof depends on

- [Single-server and full-coalition PIR must send the whole database](pir-single-server-lower-bound.md)

## Sources

- Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan, "Private Information Retrieval", Journal of the ACM, 1998.
