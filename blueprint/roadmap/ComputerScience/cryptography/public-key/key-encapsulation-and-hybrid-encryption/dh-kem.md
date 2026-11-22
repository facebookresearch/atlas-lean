# Diffie–Hellman KEM

Let $G$ be a commutative group, $g \in G$, $q \ge 1$ an integer and $H : G \to K$ a key-derivation
function; for $u \in G$ and $a \in \mathbb{Z}/q$ write $u^a$ for $u^{\bar a}$, where $\bar a$ is the
representative of $a$ in $\{0, \dots, q - 1\}$. The Diffie–Hellman KEM (Katz and Lindell,
Section 11.4.2) has a uniform secret key $x \in \mathbb{Z}/q$ and public key $h = g^x$. Encapsulation
draws a uniform $y \in \mathbb{Z}/q$ and outputs the key $H(h^y)$ with the encapsulation $g^y$;
decapsulation of $e$ gives $H(e^x)$.
