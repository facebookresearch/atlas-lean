# Baum–Sweet: explicit continued fractions of roots

Let $n \ge 0$ and let
$P, Q \in \mathbb{F}_2[x]$ with $P + Q^{2^n} \ne 0$ and $P + Q^{2^n} \ne 1$. Then some
$f \in \mathbb{F}_2((x^{-1}))$ satisfies $f^{2^n+1} + Q f^{2^n} + P f + QP + 1 = 0$ and has partial
quotients $b_0 = Q$ and $b_k = P^{2^{(k-1)n}} + Q^{2^{kn}}$ for all $k \ge 1$, that is,
$f = [Q; P + Q^{2^n}, P^{2^n} + Q^{2^{2n}}, P^{2^{2n}} + Q^{2^{3n}}, \dots]$.

The paper also claims that this root is unique, which fails: for $n = 0$, $P = x$ and $Q = 0$ the
equation $f(f + x) = 1$ has the two roots $[0; x, x, \dots]$ and $[x; x, x, \dots]$.

## Sources

- Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57, Theorem 3 (quoting Baum and Sweet) (`integers-2026-A57-thm-3`).
