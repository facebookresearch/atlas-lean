# Extending an environment

An environment is a map $e : \mathbb{N} \to \mathbb{R}$ that
assigns a real number to each de Bruijn index. For $x \in \mathbb{R}$, the extension of $e$ by $x$
sends index $0$ to $x$ and index $i + 1$ to $e(i)$ for every $i \in \mathbb{N}$.
