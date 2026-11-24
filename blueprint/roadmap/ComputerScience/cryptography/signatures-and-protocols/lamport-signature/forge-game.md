# One-time forgery game

Let $f : X \to Y$ with $X$ finite and nonempty, and let $A$ be a
one-time forger for messages of length $\ell$ with random coins in a finite nonempty set $R$. The
one-time forgery game is the distribution on $\{\mathrm{true}, \mathrm{false}\}$ obtained by drawing
a secret key $sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$ and coins $r \in R$ uniformly and
independently, and returning whether $A$ wins against $sk$ with coins $r$.
