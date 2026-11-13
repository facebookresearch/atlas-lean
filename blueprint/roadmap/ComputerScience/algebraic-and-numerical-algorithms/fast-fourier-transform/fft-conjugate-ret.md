# Conjugating around the FFT conjugates the root

Let $N = 2^d$, let $\omega \in \mathbb{C}$
be a primitive $N$-th root of unity and let $x \in \mathbb{C}^N$. Conjugating every entry of $x$,
running the FFT procedure with root $\omega$ and conjugating every entry of the result gives the
same vector as running the FFT procedure on $x$ with root $\overline{\omega}$.
