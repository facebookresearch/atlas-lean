# Foldr range xor telescope

Let $q, e : \mathbb{N} \to \mathrm{Bool}$ satisfy $e(i) = q(i) \oplus q(i+1)$ for every $i$. Then for every $r \in \mathbb{N}$ and every **seed** $b \in \mathrm{Bool}$, the right fold of $\oplus$ over $e(0), \dots, e(r-1)$ starting from $b$ is

$$
e(0) \oplus \bigl(e(1) \oplus \cdots \oplus (e(r-1) \oplus b)\bigr) = \bigl(q(0) \oplus q(r)\bigr) \oplus b .
$$

The seed cannot be dropped: at $r = 0$ the fold is $b$, while $q(0) \oplus q(0)$ is false, so with $b$ true the endpoints alone give the wrong answer.
