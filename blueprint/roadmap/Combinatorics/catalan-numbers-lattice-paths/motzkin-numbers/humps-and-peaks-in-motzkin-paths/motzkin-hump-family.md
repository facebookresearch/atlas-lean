# Motzkin paths with a marked hump, over all heights

For a natural number $n$, this is
the set of triples $(k, P, h)$ where $k$ is a natural number with
$1 \le k \le \lfloor n/2 \rfloor$, $P$ is a Motzkin path of length $n$ (a word of $n$ steps
$U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$ that ends at height $0$ and never goes below height
$0$), and $h$ is a hump of height $k$ in $P$: an up step and a later down step with only flat
steps between them, where the up step ends at height $k$, recorded by the positions of its two
steps.

This is the paper's disjoint union $\bigcup_{1 \le k \le \lfloor n/2 \rfloor} \mathcal{H}_{n,k}$,
keeping the height index $k$ with each marked path.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
