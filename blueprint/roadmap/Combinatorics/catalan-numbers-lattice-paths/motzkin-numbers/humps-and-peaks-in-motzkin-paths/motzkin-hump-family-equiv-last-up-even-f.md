# Humps correspond to last-up prefixes of twice the height

Use the steps $U = (1,1)$,
$F = (1,0)$ and $D = (1,-1)$. A Motzkin prefix of length $n$ ending at height $h$ is a word of
$n$ steps that never goes below height $0$ and ends at height $h$; a Motzkin path is a Motzkin
prefix ending at height $0$. A hump of height $k$ in a path is a pair of an up step and a later
down step with only flat steps between them, where the up step ends at height $k$; the hump is
a peak when the down step immediately follows the up step. For every natural number $n$ there
is a bijection from the set of triples $(k, P, h)$ with $1 \le k \le \lfloor n/2 \rfloor$, $P$
a Motzkin path of length $n$ and $h$ a hump of height $k$ in $P$, to the set of pairs $(k, p)$
with $1 \le k \le \lfloor n/2 \rfloor$ and $p$ a Motzkin prefix of length $n$ ending at height
$2k$ that contains a $U$ after which every step is $F$. This bijection keeps the index $k$, and
the hump $h$ is a peak exactly when the image path $p$ ends with an up step.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
