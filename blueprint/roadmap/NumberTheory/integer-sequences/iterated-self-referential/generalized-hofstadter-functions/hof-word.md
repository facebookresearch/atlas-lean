# Letters of the Hofstadter fixed-point word

For natural numbers $k$ and $n$, let $\tau_k$
be the substitution on letters in $\mathbb{N}$ that sends $k$ to the word $k\,1$ and every other
letter $i$ to $i + 1$, applied to words letter by letter, and let $\tau_k^j(k)$ be the word
obtained by applying $\tau_k$ $j$ times to the one-letter word $k$. Then $x_k[n]$ is the letter at
position $n$, counting from $0$, of the shortest word $\tau_k^j(k)$ with $j \ge 0$ that has more
than $n$ letters.

Since each word $\tau_k^j(k)$ is a prefix of $\tau_k^{j+1}(k)$, $x_k[n]$ is the letter at position
$n$ of the fixed point $x_k$ of $\tau_k$ that begins with $k$, and every word $\tau_k^j(k)$ with
more than $n$ letters has $x_k[n]$ at position $n$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Section 1.2.
