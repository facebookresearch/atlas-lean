# Encryption from a keyed function

Let $Y$ be an additive commutative group of messages
and let $f \colon X \to Y$ be a function (in the scheme, $f = F_k$ for a key $k$). The
encryption of a message $m \in Y$ with randomness $r \in X$ is the pair
$(r, f(r) + m) \in X \times Y$.

This is Construction 3.30 of Katz and Lindell, with XOR replaced by the addition of the
message group.
