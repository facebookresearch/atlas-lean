# Multiset equality via randomized product fingerprints

Encode a triple $(a,v,t)\in\mathbb{F}^{3}$ as $h_\tau(a,v,t)=a+\tau v+\tau^{2}t$. For multisets $S,S'$ of $k$ triples each, if $S\ne S'$ then for uniformly random $\tau,\gamma\in\mathbb{F}$,

$$
\Pr\Bigl[\prod_{e\in S}(\gamma-h_\tau(e))=\prod_{e\in S'}(\gamma-h_\tau(e))\Bigr]\le\frac{3k}{|\mathbb{F}|}.
$$

Thus offline memory checking reduces to a grand-product claim, provable via a layered product circuit or a hypercube product check.

## Proof sketch

Distinct triples map to distinct $h_\tau$ values except when $\tau$ is a root of one of the at most $k^{2}$ difference polynomials of degree $2$; more carefully, compare the polynomials $\prod(Y-h_\tau(e))$ in $\mathbb{F}[\tau,Y]$, which differ when $S\ne S'$ and have total degree at most $3k$, and apply Schwartz–Zippel.

## Depends on

- [Offline memory checking with timestamps](offline-memory-checking.md)

## Proof depends on

- [Multiset equality certifies read-correctness of memory](memory-checking-soundness.md)

## Sources

- Manuel Blum, Will Evans, Peter Gemmell, Sampath Kannan, Moni Naor, "Checking the Correctness of Memories", Algorithmica (1994).
- Srinath Setty, "Spartan: Efficient and General-Purpose zkSNARKs without Trusted Setup", CRYPTO (2020), IACR ePrint 2019/550.
