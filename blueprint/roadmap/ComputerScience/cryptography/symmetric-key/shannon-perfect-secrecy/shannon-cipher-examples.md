# Perfect secrecy of the additive and variable-length one-time pads and of the substitution cipher

(i) The additive one-time pad $E(k, m) = m + k$, $D(k, c) = c - k$ over any finite abelian group is perfectly secure. (ii) The variable-length one-time pad, which encrypts a message of length at most $L$ by XOR with the corresponding prefix of an $L$-bit key, is perfectly secure if and only if $L = 0$: for $L > 0$ the ciphertext length reveals the message length. (iii) The substitution cipher, which encrypts words over an alphabet $\Sigma$ letterwise with a uniformly random permutation of $\Sigma$, is not perfectly secure on words of length at least $2$ over an alphabet with at least two symbols: the ciphertext of $aa$ always has two equal letters, while that of $ab$ with $a \ne b$ never does.

## Proof sketch

(i) For fixed $m$, $k \mapsto m + k$ is a bijection. (ii) and (iii) exhibit two messages and an event with different probabilities.

## Depends on

- [The group one-time pad](../one-time-pad-over-a-finite-group/group-otp.md)

## Proof depends on

- [Characterizations of perfect security](perfect-security-characterizations.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
