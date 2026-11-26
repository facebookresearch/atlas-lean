# q-gram lower bound on edit distance

**Setting.** Let $\Sigma$ be a finite alphabet and $q\ge1$. The *$q$-gram profile* of a string $a\in\Sigma^*$ is the vector $\vec Q(a)\in\mathbb N_0^{|\Sigma|^q}$ whose coordinate at $w\in\Sigma^q$ counts the occurrences of $w$ as a substring of $a$. The *$q$-gram distance* is the $\ell_1$ distance of profiles,

$$
d_q(a,b)=\|\vec Q(a)-\vec Q(b)\|_1 .
$$

Let $d(a,b)$ denote the Levenshtein (unit-cost insert/delete/replace) edit distance.

**Theorem.** For all strings $a,b$,

$$
d_q(a,b)\le 2q\,d(a,b).
$$

In particular, for $q=3$ (the value used for short sequencing reads),

$$
d(a,b)\ \ge\ \tfrac16\,d_3(a,b).
$$

## Expansion

Induct on $k=d(a,b)$. If $k=0$ both distances vanish. Otherwise let $b'$ be the string reached after the first $k-1$ edit operations of an optimal script, so $d(a,b')=k-1$, and bound the effect of the last operation on the profile. A single substitution touches at most $q$ windows of length $q$; it removes up to $q$ $q$-grams and creates up to $q$ new ones, changing the $\ell_1$ profile distance by at most $2q$. An insertion or deletion destroys at most $q-1$ windows and creates at most $q$ (or vice versa), changing the profile by at most $2q-1$. By the triangle inequality $d_q(a,b)\le d_q(a,b')+2q\le 2q(k-1)+2q$.

The bound makes $d_q$ a cheap filter: in nearest-read searches one can rank candidates by $d_q$ (a vector computation) and evaluate the expensive edit distance only for the few candidates whose $q$-gram distance is small, since $d_q/(2q)$ never overestimates the true edit distance.

## Sources

- E. Ukkonen, "Approximate string-matching with $q$-grams and maximal matches", *Theoretical Computer Science* 92 (1992) 191–211 (general $q$).
- Petr Ryšavý, Filip Železný, "Estimating Sequence Similarity from Read Sets for Clustering Next-Generation Sequencing data", arXiv:1705.06125 (2017), Section 4, Theorem 1 (case $q=3$ with induction proof), <https://doi.org/10.48550/arXiv.1705.06125>.
