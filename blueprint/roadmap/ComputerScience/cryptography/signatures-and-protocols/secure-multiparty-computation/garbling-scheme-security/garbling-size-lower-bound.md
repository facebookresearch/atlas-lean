# Entropy lower bound on the size of garbled material

Let $c$ be an observation, $x$ a hidden value and $g$ garbled material of $m$ bits, all random variables on one probability space. If the evaluator can recover a quantity $z$ from $(c, g)$ deterministically, while in a simulated world (given $c$ alone) $z$ retains conditional Shannon entropy at least $h$ given $c$, and the real and simulated distributions of $(c, g)$ coincide, then

$$
m \ge H(z \mid c) \ge h ,
$$

so garbled material must be at least as long as the entropy it lets the evaluator recover beyond what the simulator's view fixes. In particular, garbling a lookup table or gate whose output label carries $\kappa$ bits of entropy unknown from the inputs requires $\kappa$ bits of material.

## Proof sketch

$H(z \mid c) \le H(g \mid c) \le H(g) \le m$ because $z$ is a function of $(c, g)$ and $g$ takes at most $2^m$ values.

## Depends on

- [Side-information functions and privacy notions for garbling schemes](garbling-privacy-notions.md)

## Sources

- Samee Zahur, Mike Rosulek and David Evans, "Two Halves Make a Whole: Reducing Data Transfer in Garbled Circuits Using Half Gates", Advances in Cryptology – EUROCRYPT 2015, 2015.
- David Heath, Vladimir Kolesnikov and Lucien K. L. Ng, "Garbled Circuit Lookup Tables with Logarithmic Number of Ciphertexts", Advances in Cryptology – EUROCRYPT 2024, 2024.
