# Complement symmetry of Ulam words

For a word $w$ over $\{0, 1\}$, let $\bar w$ be its
complement (every letter swapped) and let $\pi(w)$ be the integer whose binary expansion is $w$,
most significant letter first. If $w$ is an Ulam word of length $n$, then $\bar w$ is an Ulam
word and $\pi(\bar w) + \pi(w) = 2^n - 1$. Moreover, for all natural numbers $N$ and $n$ and every
$a \in \mathbb{Z}/N\mathbb{Z}$, the number of Ulam words $w$ of length $n$ with
$\pi(w) \equiv a \pmod N$ equals the number of Ulam words $w$ of length $n$ with
$\pi(w) \equiv 2^n - 1 - a \pmod N$.

For $n \ge 1$, writing $\rho_{a,N}(n)$ for the proportion of Ulam words $w$ of length $n$ with
$\pi(w) \equiv a \pmod N$ among all Ulam words of length $n$, the second statement says
$\rho_{a,N}(n) = \rho_{2^n-1-a,N}(n)$.

## Sources

- Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma, *Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 11.
