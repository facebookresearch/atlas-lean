# Gram matrix of the actions

For a matrix $V_0 \in \mathbb{R}^{d \times d}$ and vectors
$a_0, a_1, \ldots \in \mathbb{R}^d$, numbered from $0$, the Gram matrix after $t$ rounds is

$$V_t = V_0 + \sum_{k < t} a_k a_k^{\mathsf T},$$

the sum of $V_0$ and of the first $t$ outer products $a_k a_k^{\mathsf T}$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Lemma 19.4, the matrices $V_t$, whose actions are numbered from $1$: the book's $a_{k+1}$ is $a_k$ here. <https://tor-lattimore.com/downloads/book/book.pdf>
