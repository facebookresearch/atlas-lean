# One-time forger

A one-time forger for messages of length $\ell$, with random coins in a
set $R$, consists of two maps. The first takes a public key
$pk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to Y$ and coins $r \in R$ and returns the message
$m \in \{0, 1\}^\ell$ whose signature the forger requests. The second takes a public key, a
signature $\sigma \in X^\ell$ and coins $r$ and returns a message $m' \in \{0, 1\}^\ell$ together
with a signature $\sigma' \in X^\ell$.
