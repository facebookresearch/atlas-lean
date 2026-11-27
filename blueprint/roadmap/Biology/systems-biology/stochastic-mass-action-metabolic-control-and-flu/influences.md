# Interaction graph of a Boolean network

Let $n \in \mathbb{N}$ and $f \colon \{0, 1\}^n \to \{0, 1\}^n$. In the interaction graph of $f$ there is an edge $j \to i$ when the $i$-th coordinate of $f$
depends on the $j$-th variable: $f(x')_i \ne f(x)_i$ for some $x \in \{0, 1\}^n$, where $x'$ is $x$ with
its $j$-th coordinate flipped.
