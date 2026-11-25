# Correctness of Lamport signatures

Let $f : X \to Y$. For every secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$ and every message $m \in \{0, 1\}^\ell$, the
Lamport signature of $m$ under $sk$ is valid for $m$ under the public key of $sk$.
