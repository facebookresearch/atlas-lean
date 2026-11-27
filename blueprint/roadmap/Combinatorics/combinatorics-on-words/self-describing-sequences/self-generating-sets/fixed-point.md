# Fixed-point sets for a seed and generators

Let $F$ be a finite set of functions
$\mathbb{N} \to \mathbb{N}$ and let $s \in \mathbb{N}$. A set $C \subseteq \mathbb{N}$ is a
fixed-point set for $F$ and $s$ when, for every $y \in \mathbb{N}$, $y \in C$ if and only if
$y = s$ or $y = f(x)$ for some $f \in F$ and some $x \in C$; equivalently,
$C = \{s\} \cup \bigcup_{f \in F} f(C)$.
