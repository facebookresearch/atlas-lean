# Correctness of ElGamal

Let $G$ be a commutative group, $g \in G$ and $q$ a natural
number. For $a \in \mathbb{Z}/q\mathbb{Z}$ and $c \in G$ write $c^a$ for
$c^{\operatorname{val}(a)}$, where $\operatorname{val}(a) \in \mathbb{N}$ is the representative
of $a$ in $\{0, \dots, q-1\}$ if $q \ge 1$ and $|a|$ if $q = 0$. For every secret key
$x \in \mathbb{Z}/q\mathbb{Z}$, every message $m \in G$ and every encryption randomness
$y \in \mathbb{Z}/q\mathbb{Z}$, decrypting with $x$ the ElGamal encryption of $m$ under the
public key $g^x$ with randomness $y$ returns $m$.
