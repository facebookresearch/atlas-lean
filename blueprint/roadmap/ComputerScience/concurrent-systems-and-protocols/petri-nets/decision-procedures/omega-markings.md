# ω-markings of a Petri net

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with places $P$. Extend $\mathbb{N}$ by a symbol $\omega$ with $n + \omega = \omega + n = \omega$, $\omega + \omega = \omega$, $\omega - n = \omega$, $0 \cdot \omega = 0$, $n \cdot \omega = \omega \cdot n = \omega$ for $n \ge 1$, and $n \le \omega$, $\omega \le \omega$ for every $n \in \mathbb{N}$; $\omega - \omega$ is undefined. An *ω-marking* of $N$ is a map $M : P \to \mathbb{N} \cup \{\omega\}$; a place $s$ is an *ω-place* of $M$ if $M(s) = \omega$ and a *normal place* otherwise. A transition $t$ is enabled at $M$ if $M(s) > 0$ for every input place $s$ of $t$, and firing it yields the ω-marking $M'$ with $M'(s) = M(s) - 1$ for $s \in {}^\bullet t \setminus t^\bullet$, $M'(s) = M(s) + 1$ for $s \in t^\bullet \setminus {}^\bullet t$ and $M'(s) = M(s)$ otherwise; so firing never changes the value of an ω-place. ω-markings are ordered placewise. On an ordinary net these ω-markings and this firing rule are those of [the coverability tree](coverability-tree.md) for arcs of weight $1$.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [The coverability tree](coverability-tree.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Section 3.2.2, paragraph "Coverability graphs" (the extended arithmetic, ω-markings and their firing rule), p. 51, and Definition 3.2.6, p. 52.
