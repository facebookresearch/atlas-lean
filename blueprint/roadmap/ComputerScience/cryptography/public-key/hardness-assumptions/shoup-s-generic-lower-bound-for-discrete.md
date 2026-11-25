# Shoup's generic lower bound for discrete logarithms

In the *generic group model*, a cyclic group $G = \langle g \rangle$ of order $N$ is accessed only through a black box $B$ that represents each element by an
identification string $\mathrm{id}(h) \in \{0,1\}^n$, for a uniformly random injective map $\mathrm{id} : G \to \{0,1\}^n$ with $n = O(\log N)$, and supports the operations
identity, inverse and composition on these strings. A *generic algorithm* computes only through calls to $B$; it may use random coins $\tau$ and knows $N$.

**Theorem (Shoup).** Let $p$ be the largest prime factor of $N$. Let $A$ be a randomized generic algorithm that, given $\mathrm{id}(g)$ and $\mathrm{id}(g^x)$, makes at
most $m - 4\lceil \log_2 N \rceil$ calls to $B$, for an integer $m$. For $x$ uniform in $\mathbb{Z}/N\mathbb{Z}$,

$$\Pr_{x, \mathrm{id}, \tau}\left[A(\mathrm{id}(g), \mathrm{id}(g^x)) = x\right] < \frac{m^2}{2p}.$$

Consequently a generic algorithm needs $\Omega(\sqrt p)$ group operations to compute discrete logarithms with constant success probability.

## Depends on

- [Discrete-logarithm experiment](dlog-game.md)

## Sources

- A. V. Sutherland, *18.783 Elliptic Curves*, Lecture 11: generic algorithms for the discrete logarithm problem, MIT, 2013, <https://math.mit.edu/classes/18.783/2013/LectureNotes11.pdf>: the generic group model with a random identification map, Theorem 11.1 with its proof, and the corollary on expected running time.
