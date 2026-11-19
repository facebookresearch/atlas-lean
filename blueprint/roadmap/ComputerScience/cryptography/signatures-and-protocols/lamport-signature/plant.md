# Planted public key

Let $f : X \to Y$. Given a secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$, a position $(i, b)$ and a value $y \in Y$, the
planted public key takes the value $y$ at $(i, b)$ and the value $f(sk(j, c))$ at every other
position $(j, c)$.
